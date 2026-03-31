const video = document.getElementById("video");
const canvas = document.getElementById("canvas");
const ctx = canvas.getContext("2d", { alpha: false });
const info = document.getElementById("info");
const audioBtn = document.getElementById("start-audio-btn");
const isMobile = /Android|webOS|iPhone|iPad|iPod|BlackBerry|IEMobile|Opera Mini/i.test(navigator.userAgent);

let lastTime = performance.now();
let renderFps = 0;
let detectBusy = false;
let latestHandResult = null;
let latestFaceResult = null;
let smoothedHands = [];
let stableHandedness = [];
let handsMissingSince = null;
let lastFaceLandmarks = null;
let lastFaceSeenAt = 0;
let lightOn = false;
let cachedGlowGradient = null;
let cachedGlowWidth = 0;
let cachedGlowHeight = 0;
let lastDetectAt = 0;
let detectPhase = 0;
let lastPinchHitTestAt = 0;
let lastInfoUpdateAt = 0;

const PERF = {
    detectIntervalMs: isMobile ? 66 : 33,
    maxBoxes: isMobile ? 28 : 96,
    handModelComplexity: isMobile ? 0 : 1,
    faceRefineLandmarks: !isMobile,
    pinchHitTestMs: isMobile ? 90 : 45,
    infoRefreshMs: 120,
    handHoldMs: 140,
    faceHoldMs: 140
};

const BOX_VERTICES = [
    { x: -1, y: -1, z: -1 },
    { x: 1, y: -1, z: -1 },
    { x: 1, y: 1, z: -1 },
    { x: -1, y: 1, z: -1 },
    { x: -1, y: -1, z: 1 },
    { x: 1, y: -1, z: 1 },
    { x: 1, y: 1, z: 1 },
    { x: -1, y: 1, z: 1 }
];

const BOX_FACES = [
    { i: [0, 1, 2, 3], c: "#1976D2" },
    { i: [4, 5, 6, 7], c: "#42A5F5" },
    { i: [0, 1, 5, 4], c: "#90CAF9" },
    { i: [2, 3, 7, 6], c: "#0D47A1" },
    { i: [0, 3, 7, 4], c: "#1E88E5" },
    { i: [1, 2, 6, 5], c: "#1565C0" }
];

const FACE_NORMALS = [
    { x: 0, y: 0, z: -1 },
    { x: 0, y: 0, z: 1 },
    { x: 0, y: -1, z: 0 },
    { x: 0, y: 1, z: 0 },
    { x: -1, y: 0, z: 0 },
    { x: 1, y: 0, z: 0 }
];

// State cho khối 3D
let boxes3D = [];
let rotationAngle = 0;
let rotationAngleY = 0; 
let lastBoxTime = 0;
const BOX_SIZE = 40;
const BOX_ADD_COOLDOWN_MS = 120;
let wasZeroFingers = false;
let lastHandX = 0;
let lastHandY = 0; 
let leftFingerCandidate = null;
let leftFingerStableFrames = 0;
let leftFingerStable = null;
let lastLeftClearAt = 0;
const LEFT_ACTION_STABLE_FRAMES = 3;
const LEFT_CLEAR_COOLDOWN_MS = 500;
const FINGER_UP_TOLERANCE = 0.02;
const THUMB_UP_THRESHOLD = 0.02;
const PINCH_DISTANCE_THRESHOLD = 0.065;
const OK_GESTURE_DISTANCE_THRESHOLD = 0.07;

// Config cảnh báo buồn ngủ
const EAR_MIN_THRESHOLD = 0.14;
const EAR_MAX_THRESHOLD = 0.22;
const EAR_RATIO_FROM_BASELINE = 0.72;
const CLOSED_DURATION_MS_THRESHOLD = 3000;
const EYE_OPEN_CONFIRM_MS = 450;
const EAR_CALIBRATION_FRAMES = 20;
let earBaseline = null;
let smoothedEAR = null;
let earStableFrames = 0;
let dynamicEarThreshold = EAR_MAX_THRESHOLD;
let eyeClosedSince = null;
let eyeOpenSince = null;
let faceStatus = "Tỉnh táo";
let isSleeping = false;

// Audio cảnh báo (Web Audio API)
const audioCtx = new (window.AudioContext || window.webkitAudioContext)();
let alarmInterval = null;

audioBtn.addEventListener('click', () => {
    if (audioCtx.state === 'suspended') audioCtx.resume();
    audioBtn.style.display = 'none';
});

function playBeep() {
    if (audioCtx.state === 'suspended') return;
    const osc = audioCtx.createOscillator();
    const gain = audioCtx.createGain();
    osc.type = 'square'; 
    osc.frequency.setValueAtTime(880, audioCtx.currentTime); 
    gain.gain.setValueAtTime(0.5, audioCtx.currentTime); 
    gain.gain.exponentialRampToValueAtTime(0.01, audioCtx.currentTime + 0.3); 
    osc.connect(gain);
    gain.connect(audioCtx.destination);
    osc.start();
    osc.stop(audioCtx.currentTime + 0.3);
}

function resize() {
    const viewportWidth = Math.round(window.visualViewport?.width || window.innerWidth);
    const viewportHeight = Math.round(window.visualViewport?.height || window.innerHeight);
    if (canvas.width === viewportWidth && canvas.height === viewportHeight) return;
    canvas.width = viewportWidth;
    canvas.height = viewportHeight;
    canvas.style.width = `${viewportWidth}px`;
    canvas.style.height = `${viewportHeight}px`;
    cachedGlowGradient = null;
    cachedGlowWidth = 0;
    cachedGlowHeight = 0;
}
window.addEventListener("resize", resize);
if (isMobile) window.visualViewport?.addEventListener("resize", resize);
resize();

function clamp(value, min, max) {
    return Math.min(max, Math.max(min, value));
}

function hasBoxAt(x, y, z, tolerance = BOX_SIZE * 0.28) {
    return boxes3D.some(b =>
        Math.abs(b.gridX - x) <= tolerance &&
        Math.abs(b.gridY - y) <= tolerance &&
        Math.abs((b.z || 0) - z) <= tolerance
    );
}

function addBoxAt(x, y, z) {
    if (hasBoxAt(x, y, z)) return false;
    boxes3D.push({ gridX: x, gridY: y, z });
    if (boxes3D.length > PERF.maxBoxes) boxes3D.shift();
    lastBoxTime = performance.now();
    return true;
}

function getUiScale() {
    return clamp(canvas.width / 1280, 0.75, 1);
}

function getDrawRect() {
    const vw = video.videoWidth || 640;
    const vh = video.videoHeight || 480;
    const scale = Math.max(canvas.width / vw, canvas.height / vh);
    const drawWidth = vw * scale;
    const drawHeight = vh * scale;
    const offsetX = (canvas.width - drawWidth) / 2;
    const offsetY = (canvas.height - drawHeight) / 2;
    return { vw, vh, drawWidth, drawHeight, offsetX, offsetY };
}

function mapPoint(p, rect) {
    return { x: rect.offsetX + p.x * rect.drawWidth, y: rect.offsetY + p.y * rect.drawHeight };
}

function smoothPoint(prev, next, alpha = 0.6) { 
    if (!prev) return { x: next.x, y: next.y, z: next.z || 0 };
    return { 
        x: prev.x * alpha + next.x * (1 - alpha), 
        y: prev.y * alpha + next.y * (1 - alpha), 
        z: (prev.z || 0) * alpha + (next.z || 0) * (1 - alpha) 
    };
}

function updateSmoothedHands(handLandmarks) {
    if (!handLandmarks || handLandmarks.length === 0) {
        if (handsMissingSince === null) handsMissingSince = performance.now();
        if (performance.now() - handsMissingSince > PERF.handHoldMs) {
            smoothedHands = [];
            stableHandedness = [];
            leftFingerCandidate = null;
            leftFingerStableFrames = 0;
            leftFingerStable = null;
            wasZeroFingers = false;
        }
        return;
    }
    handsMissingSince = null;
    if (smoothedHands.length !== handLandmarks.length) {
        smoothedHands = handLandmarks.map(hand => hand.map(pt => ({...pt})));
        return;
    }
    smoothedHands = handLandmarks.map((hand, handIndex) => {
        const previousHand = smoothedHands[handIndex];
        return hand.map((point, pointIndex) => smoothPoint(previousHand[pointIndex], point, 0.6));
    });
}

function isFingerUp(hand, tipIndex, pipIndex) { return hand[tipIndex].y < (hand[pipIndex].y + FINGER_UP_TOLERANCE); }
function isThumbUp(hand) { return Math.abs(hand[4].x - hand[3].x) > THUMB_UP_THRESHOLD; }

function countRaisedFingers(hand) {
    let count = 0;
    if (isThumbUp(hand)) count++;
    if (isFingerUp(hand, 8, 6)) count++;
    if (isFingerUp(hand, 12, 10)) count++;
    if (isFingerUp(hand, 16, 14)) count++;
    if (isFingerUp(hand, 20, 18)) count++;
    return count;
}

function detectGesture(hand) {
    const middle = isFingerUp(hand, 12, 10);
    const ring = isFingerUp(hand, 16, 14);
    const pinky = isFingerUp(hand, 20, 18);
    const count = countRaisedFingers(hand);
    const distThumbIndex = Math.hypot(hand[4].x - hand[8].x, hand[4].y - hand[8].y);
    if (distThumbIndex < OK_GESTURE_DISTANCE_THRESHOLD && middle && ring && pinky) return "OK 👌";
    if (count === 2) return "HI 👋";
    if (count === 4) return "HELP 🆘";
    return null;
}

function getDistance(p1, p2) { return Math.sqrt(Math.pow(p1.x - p2.x, 2) + Math.pow(p1.y - p2.y, 2)); }

function calculateEAR(eyeIdx, face) {
    const p1 = face[eyeIdx[0]], p2 = face[eyeIdx[1]], p3 = face[eyeIdx[2]], p4 = face[eyeIdx[3]], p5 = face[eyeIdx[4]], p6 = face[eyeIdx[5]];
    const v1 = getDistance(p2, p6), v2 = getDistance(p3, p5), h = getDistance(p1, p4);
    return (v1 + v2) / (2.0 * h);
}

function solveInverseBilinearInterpolation(p0, p1, p2, p3, p, maxIterations = 20, tolerance = 0.001) {
    let u = 0.5; let v = 0.5;
    const solveF = (u, v) => {
        const p_uv_x = (1 - u) * (1 - v) * p0.x + u * (1 - v) * p1.x + u * v * p2.x + (1 - u) * v * p3.x;
        const p_uv_y = (1 - u) * (1 - v) * p0.y + u * (1 - v) * p1.y + u * v * p2.y + (1 - u) * v * p3.y;
        return { x: p_uv_x - p.x, y: p_uv_y - p.y };
    };
    const solveJacobian = (u, v) => {
        const dfdu_x = -(1 - v) * p0.x + (1 - v) * p1.x + v * p2.x - v * p3.x;
        const dfdv_x = -(1 - u) * p0.x - u * p1.x + u * p2.x + (1 - u) * p3.x;
        const dfdu_y = -(1 - v) * p0.y + (1 - v) * p1.y + v * p2.y - v * p3.y;
        const dfdv_y = -(1 - u) * p0.y - u * p1.y + u * p2.y + (1 - u) * p3.y;
        return { du_x: dfdu_x, dv_x: dfdv_x, du_y: dfdu_y, dv_y: dfdv_y };
    };
    for (let i = 0; i < maxIterations; i++) {
        const f = solveF(u, v); const j = solveJacobian(u, v);
        const det = j.du_x * j.dv_y - j.dv_x * j.du_y;
        if (Math.abs(det) < 1e-6) break; 
        const du = (-f.x * j.dv_y + f.y * j.dv_x) / det;
        const dv = (-j.du_x * f.y + j.du_y * f.x) / det;
        u += du; v += dv;
        if (Math.abs(du) < tolerance && Math.abs(dv) < tolerance) break; 
    }
    return { u, v };
}

function scheduleDraw() {
    if (typeof video.requestVideoFrameCallback === "function") {
        video.requestVideoFrameCallback(() => {
            drawScene();
            scheduleDraw();
        });
    } else {
        requestAnimationFrame(() => {
            drawScene();
            scheduleDraw();
        });
    }
}

async function startCamera() {
    try {
        const videoConstraints = isMobile
            ? { facingMode: { ideal: "user" }, width: { ideal: 640, max: 960 }, height: { ideal: 360, max: 540 } }
            : { facingMode: "user", width: { ideal: 1280 }, height: { ideal: 720 } };
        const stream = await navigator.mediaDevices.getUserMedia({ video: videoConstraints, audio: false });
        video.srcObject = stream; await video.play(); scheduleDraw(); detectLoop();
    } catch (err) { info.innerText = "Không mở được camera: " + err.message; }
}

const hands = new Hands({ locateFile: f => `https://cdn.jsdelivr.net/npm/@mediapipe/hands/${f}` });
hands.setOptions({
    maxNumHands: 2,
    modelComplexity: PERF.handModelComplexity,
    minDetectionConfidence: 0.5,
    minTrackingConfidence: 0.5,
    selfieMode: true
});
hands.onResults(res => { 
    latestHandResult = res; 
    if (res.multiHandedness && res.multiHandedness.length > 0) {
        stableHandedness = res.multiHandedness.map(h => ({ ...h }));
    }
    updateSmoothedHands(res.multiHandLandmarks || []); 
});

const faceMesh = new FaceMesh({ locateFile: f => `https://cdn.jsdelivr.net/npm/@mediapipe/face_mesh/${f}` });
faceMesh.setOptions({
    maxNumFaces: 1,
    refineLandmarks: PERF.faceRefineLandmarks,
    minDetectionConfidence: 0.45,
    minTrackingConfidence: 0.45,
    selfieMode: true
});
faceMesh.onResults(res => {
    latestFaceResult = res;
    const face = res?.multiFaceLandmarks?.[0];
    if (face) {
        lastFaceLandmarks = face;
        lastFaceSeenAt = performance.now();
    }
});

function drawScene() {
    if (video.readyState < 2) return;
        const rect = getDrawRect();
        const uiScale = getUiScale();
        const baseLabelFont = Math.round(16 * uiScale);
        const gestureFont = Math.round(26 * uiScale);
        const statusFont = Math.round(26 * uiScale);
        const strokeThin = clamp(1.5 * uiScale, 1.1, 1.5);
        const safeMargin = Math.round(clamp(canvas.width * 0.02, 12, 24));
        ctx.clearRect(0, 0, canvas.width, canvas.height);
        ctx.save(); ctx.translate(rect.offsetX + rect.drawWidth, rect.offsetY); ctx.scale(-1, 1);
        ctx.drawImage(video, 0, 0, rect.drawWidth, rect.drawHeight); ctx.restore();

        const now = performance.now();
        let faceFound = false;
        const face = latestFaceResult?.multiFaceLandmarks?.[0] || ((now - lastFaceSeenAt) <= PERF.faceHoldMs ? lastFaceLandmarks : null);
        if (face) {
            faceFound = true;
            const avgEARRaw = (calculateEAR([33, 160, 158, 133, 153, 144], face) + calculateEAR([362, 385, 387, 263, 373, 380], face)) / 2.0;
            if (Number.isFinite(avgEARRaw) && avgEARRaw > 0) {
                smoothedEAR = smoothedEAR === null ? avgEARRaw : (smoothedEAR * 0.75 + avgEARRaw * 0.25);
                if (earBaseline === null) {
                    earBaseline = smoothedEAR;
                } else {
                    const alpha = smoothedEAR > earBaseline ? 0.08 : 0.01;
                    earBaseline = earBaseline * (1 - alpha) + smoothedEAR * alpha;
                }
                dynamicEarThreshold = clamp(earBaseline * EAR_RATIO_FROM_BASELINE, EAR_MIN_THRESHOLD, EAR_MAX_THRESHOLD);
                earStableFrames++;
                const isCalibrated = earStableFrames >= EAR_CALIBRATION_FRAMES;

                if (isCalibrated && smoothedEAR < dynamicEarThreshold) {
                    eyeOpenSince = null;
                    if (eyeClosedSince === null) eyeClosedSince = now;
                    isSleeping = (now - eyeClosedSince) >= CLOSED_DURATION_MS_THRESHOLD;
                    faceStatus = isSleeping ? "BUỒN NGỦ!" : "Đang nhắm mắt...";
                } else {
                    eyeClosedSince = null;
                    if (isSleeping) {
                        if (eyeOpenSince === null) eyeOpenSince = now;
                        if ((now - eyeOpenSince) >= EYE_OPEN_CONFIRM_MS) {
                            isSleeping = false;
                            faceStatus = isCalibrated ? "Tỉnh táo" : "Đang hiệu chỉnh mắt...";
                        } else {
                            faceStatus = "BUỒN NGỦ!";
                        }
                    } else {
                        eyeOpenSince = null;
                        faceStatus = isCalibrated ? "Tỉnh táo" : "Đang hiệu chỉnh mắt...";
                    }
                }
            } else {
                eyeClosedSince = null;
                if (isSleeping) {
                    if (eyeOpenSince === null) eyeOpenSince = now;
                    if ((now - eyeOpenSince) >= EYE_OPEN_CONFIRM_MS) {
                        isSleeping = false;
                        faceStatus = "Đang theo dõi mắt...";
                    } else {
                        faceStatus = "BUỒN NGỦ!";
                    }
                } else {
                    eyeOpenSince = null;
                    faceStatus = "Đang theo dõi mắt...";
                }
            }
        } else {
            eyeClosedSince = null;
            if (isSleeping) {
                if (eyeOpenSince === null) eyeOpenSince = now;
                if ((now - eyeOpenSince) >= EYE_OPEN_CONFIRM_MS) {
                    isSleeping = false;
                    faceStatus = "Đang theo dõi mặt...";
                } else {
                    faceStatus = "BUỒN NGỦ!";
                }
            } else {
                eyeOpenSince = null;
                faceStatus = "Đang theo dõi mặt...";
            }
        }

        if (isSleeping) { if (!alarmInterval) { playBeep(); alarmInterval = setInterval(playBeep, 400); } }
        else { if (alarmInterval) { clearInterval(alarmInterval); alarmInterval = null; } }

        let facesToDraw = [];
        const cx = canvas.width / 2; const cy = canvas.height / 2;
        const cosX = Math.cos(rotationAngle);
        const sinX = Math.sin(rotationAngle);
        const cosY = Math.cos(rotationAngleY);
        const sinY = Math.sin(rotationAngleY);

        if (boxes3D.length > 0) {
            boxes3D.forEach(b => {
                let projected = BOX_VERTICES.map(v => {
                    let vx = (v.x * BOX_SIZE / 2) + (b.gridX - cx);
                    let vy = (v.y * BOX_SIZE / 2) + (b.gridY - cy);
                    let vz = (v.z * BOX_SIZE / 2) + b.z;
                    let tx = vx * cosX - vz * sinX;
                    let tz = vx * sinX + vz * cosX;
                    vx = tx; vz = tz;
                    let ty = vy * cosY - vz * sinY;
                    vz = vy * sinY + vz * cosY;
                    vy = ty;
                    return { x: vx + cx, y: vy + cy, z: vz };
                });
                BOX_FACES.forEach((f, i) => {
                    const p0 = projected[f.i[0]];
                    const p1 = projected[f.i[1]];
                    const p2 = projected[f.i[2]];
                    const p3 = projected[f.i[3]];
                    const centerX = (p0.x + p1.x + p2.x + p3.x) / 4;
                    const centerY = (p0.y + p1.y + p2.y + p3.y) / 4;
                    const minX = Math.min(p0.x, p1.x, p2.x, p3.x);
                    const maxX = Math.max(p0.x, p1.x, p2.x, p3.x);
                    const minY = Math.min(p0.y, p1.y, p2.y, p3.y);
                    const maxY = Math.max(p0.y, p1.y, p2.y, p3.y);
                    facesToDraw.push({
                        z: (p0.z + p1.z + p2.z + p3.z) / 4,
                        pts: [p0, p1, p2, p3],
                        sourceBox: b,
                        faceIndex: i,
                        color: f.c,
                        centerX,
                        centerY,
                        minX,
                        maxX,
                        minY,
                        maxY
                    });
                });
            });
        }

        // Xử lý tay 
        if (smoothedHands.length > 0) {
            smoothedHands.forEach((hand, handIdx) => {
                const label = stableHandedness[handIdx]?.label || latestHandResult?.multiHandedness[handIdx]?.label || "Unknown";
                const fingersUp = countRaisedFingers(hand);
                const mappedPoints = hand.map(pt => mapPoint(pt, rect));
                const wrist = mappedPoints[0];
                const labelOffsetX = Math.round(15 * uiScale);
                const labelOffsetY = Math.round(15 * uiScale);

                ctx.fillStyle = "#ffffff"; ctx.font = `bold ${baseLabelFont}px sans-serif`;
                ctx.fillText(`Tay ${handIdx + 1} (${label}) | ${fingersUp} ngón`, wrist.x + labelOffsetX, wrist.y - labelOffsetY);

                if (label === "Left") {
                    if (leftFingerCandidate === fingersUp) leftFingerStableFrames++;
                    else {
                        leftFingerCandidate = fingersUp;
                        leftFingerStableFrames = 1;
                    }
                    if (leftFingerStableFrames >= LEFT_ACTION_STABLE_FRAMES) {
                        leftFingerStable = leftFingerCandidate;
                    }
                    if (leftFingerStable === 5 && (now - lastLeftClearAt) > LEFT_CLEAR_COOLDOWN_MS) {
                        boxes3D = [];
                        lastLeftClearAt = now;
                    }
                    if (leftFingerStable === 1) lightOn = true;
                    else if (leftFingerStable === 0) lightOn = false;
                    const gst = detectGesture(hand);
                    if (gst) { ctx.fillStyle = "#FFD700"; ctx.font = `bold ${gestureFont}px sans-serif`; ctx.fillText(gst, wrist.x + labelOffsetX, wrist.y - Math.round(40 * uiScale)); }
                }

                if (label === "Right") {
                    if (fingersUp === 0) {
                        if (wasZeroFingers) { rotationAngle += (hand[0].x - lastHandX) * 4; rotationAngleY += (hand[0].y - lastHandY) * 4; }
                        lastHandX = hand[0].x; lastHandY = hand[0].y; wasZeroFingers = true;
                    } else if (wasZeroFingers) {
                        boxes3D.forEach(b => {
                            let vx = b.gridX - cx, vy = b.gridY - cy, vz = b.z || 0;
                            let tx = vx * Math.cos(rotationAngle) - vz * Math.sin(rotationAngle);
                            let tz = vx * Math.sin(rotationAngle) + vz * Math.cos(rotationAngle);
                            vx = tx; vz = tz;
                            let ty = vy * Math.cos(rotationAngleY) - vz * Math.sin(rotationAngleY);
                            vz = vy * Math.sin(rotationAngleY) + vz * Math.cos(rotationAngleY);
                            vy = ty;
                            b.gridX = vx + cx; b.gridY = vy + cy; b.z = vz;
                        });
                        rotationAngle = 0; rotationAngleY = 0; wasZeroFingers = false;
                    }

                    const distPinch = Math.hypot(hand[4].x - hand[8].x, hand[4].y - hand[8].y);
                    if (distPinch < PINCH_DISTANCE_THRESHOLD && performance.now() - lastPinchHitTestAt >= PERF.pinchHitTestMs) {
                        lastPinchHitTestAt = performance.now();
                        const mx = (mappedPoints[4].x + mappedPoints[8].x) / 2, my = (mappedPoints[4].y + mappedPoints[8].y) / 2;
                        let hit = null;
                        let hitZ = -Infinity;
                        const hitPadding = Math.round(clamp(10 * uiScale, 8, 14));
                        for (let i = 0; i < facesToDraw.length; i++) {
                            const f = facesToDraw[i];
                            if (mx < (f.minX - hitPadding) || mx > (f.maxX + hitPadding) || my < (f.minY - hitPadding) || my > (f.maxY + hitPadding)) continue;
                            ctx.beginPath(); ctx.moveTo(f.pts[0].x, f.pts[0].y); ctx.lineTo(f.pts[1].x, f.pts[1].y); ctx.lineTo(f.pts[2].x, f.pts[2].y); ctx.lineTo(f.pts[3].x, f.pts[3].y); ctx.closePath();
                            const inPath = ctx.isPointInPath(mx, my);
                            if (inPath && f.z > hitZ) {
                                hit = f;
                                hitZ = f.z;
                            }
                        }
                        if (!hit && facesToDraw.length > 0) {
                            let best = null;
                            let bestDist = Infinity;
                            for (let i = 0; i < facesToDraw.length; i++) {
                                const f = facesToDraw[i];
                                const dx = f.centerX - mx;
                                const dy = f.centerY - my;
                                const d = dx * dx + dy * dy;
                                if (d < bestDist) {
                                    bestDist = d;
                                    best = f;
                                }
                            }
                            const maxFallbackDist = (BOX_SIZE * 1.25) * (BOX_SIZE * 1.25);
                            if (best && bestDist <= maxFallbackDist) hit = best;
                        }
                        if (performance.now() - lastBoxTime > BOX_ADD_COOLDOWN_MS) {
                            if (hit) {
                                const normal = FACE_NORMALS[hit.faceIndex] || { x: 0, y: 0, z: 1 };
                                const nextX = hit.sourceBox.gridX + normal.x * BOX_SIZE;
                                const nextY = hit.sourceBox.gridY + normal.y * BOX_SIZE;
                                const nextZ = (hit.sourceBox.z || 0) + normal.z * BOX_SIZE;
                                addBoxAt(nextX, nextY, nextZ);
                            } else if (boxes3D.length === 0) {
                                const gx = Math.round(mx / BOX_SIZE) * BOX_SIZE;
                                const gy = Math.round(my / BOX_SIZE) * BOX_SIZE;
                                addBoxAt(gx, gy, 0);
                            }
                        }
                    }
                }
            });
        }

        // Render khối 3D (không dùng face drawings nữa)
        if (facesToDraw.length > 0) {
            facesToDraw.sort((a, b) => a.z - b.z);
            facesToDraw.forEach(f => {
                ctx.fillStyle = f.color; ctx.strokeStyle = "rgba(255, 255, 255, 0.8)"; ctx.lineWidth = strokeThin; ctx.beginPath();
                ctx.moveTo(f.pts[0].x, f.pts[0].y); ctx.lineTo(f.pts[1].x, f.pts[1].y); ctx.lineTo(f.pts[2].x, f.pts[2].y); ctx.lineTo(f.pts[3].x, f.pts[3].y); ctx.closePath();
                ctx.fill(); ctx.stroke();
            });
        }

        if (lightOn) {
            if (!cachedGlowGradient || cachedGlowWidth !== canvas.width || cachedGlowHeight !== canvas.height) {
                cachedGlowGradient = ctx.createRadialGradient(cx, cy, Math.round(clamp(40 * uiScale, 24, 40)), cx, cy, Math.max(canvas.width, canvas.height) / 1.3);
                cachedGlowGradient.addColorStop(0, "rgba(211,255,180,0.3)");
                cachedGlowGradient.addColorStop(1, "rgba(255,220,80,0)");
                cachedGlowWidth = canvas.width;
                cachedGlowHeight = canvas.height;
            }
            ctx.fillStyle = cachedGlowGradient;
            ctx.fillRect(0, 0, canvas.width, canvas.height);
        }

        ctx.fillStyle = isSleeping ? "#ff3333" : (faceFound ? "#00ffcc" : "#aaaaaa"); ctx.font = `bold ${statusFont}px sans-serif`;
        ctx.fillText(`Trạng thái: ${faceStatus}`, safeMargin, safeMargin + statusFont);
        if (isSleeping) {
            ctx.fillStyle = "rgba(255, 0, 0, 0.35)"; ctx.fillRect(0, 0, canvas.width, canvas.height);
            ctx.fillStyle = "#ffffff";
            let warningFont = Math.round(clamp(canvas.width * 0.08, 24, 55));
            let warningText = "⚠️ CẢNH BÁO BUỒN NGỦ ⚠️";
            ctx.font = `bold ${warningFont}px sans-serif`;
            while (ctx.measureText(warningText).width > canvas.width - safeMargin * 2 && warningFont > 18) {
                warningFont -= 2;
                ctx.font = `bold ${warningFont}px sans-serif`;
            }
            ctx.textAlign = "center";
            ctx.fillText(warningText, cx, cy);
            ctx.textAlign = "left";
        }
        const frameNow = performance.now();
        renderFps = 1000 / (frameNow - lastTime);
        lastTime = frameNow;
        if (frameNow - lastInfoUpdateAt >= PERF.infoRefreshMs) {
            info.innerText = `FPS: ${renderFps.toFixed(1)} | Tay: ${smoothedHands.length} | Mặt: ${faceStatus}`;
            lastInfoUpdateAt = frameNow;
        }
}

async function detectLoop() {
    const now = performance.now();
    if (video.readyState >= 2 && !detectBusy && (now - lastDetectAt) >= PERF.detectIntervalMs) {
        detectBusy = true;
        lastDetectAt = now;
        try {
            if (isMobile) {
                if (detectPhase === 0) await hands.send({ image: video });
                else await faceMesh.send({ image: video });
                detectPhase = (detectPhase + 1) % 2;
            } else {
                await hands.send({ image: video });
                await faceMesh.send({ image: video });
            }
        }
        catch(e) { console.error(e); }
        finally { detectBusy = false; }
    }
    const elapsed = performance.now() - now;
    const waitMs = video.readyState >= 2 ? Math.max(8, PERF.detectIntervalMs - elapsed) : 40;
    setTimeout(detectLoop, waitMs);
}
startCamera();
