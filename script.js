const video = document.getElementById("video");
const canvas = document.getElementById("canvas");
const ctx = canvas.getContext("2d");
const info = document.getElementById("info");
const audioBtn = document.getElementById("start-audio-btn");
const isMobile = /Android|webOS|iPhone|iPad|iPod|BlackBerry|IEMobile|Opera Mini/i.test(navigator.userAgent);

let lastTime = performance.now();
let renderFps = 0;
let detectBusy = false;
let latestHandResult = null;
let latestFaceResult = null;
let smoothedHands = [];
let lightOn = false;

// State cho khối 3D
let boxes3D = [];
let rotationAngle = 0;
let rotationAngleY = 0; 
let lastBoxTime = 0;
const BOX_SIZE = 40;
let wasZeroFingers = false;
let lastHandX = 0;
let lastHandY = 0; 

// Config cảnh báo buồn ngủ
let eyeClosedFrames = 0;
const EAR_THRESHOLD = 0.22; 
const CLOSED_FRAMES_THRESHOLD = 15; 
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

const HAND_CONNECTIONS = [
    [0, 1], [1, 2], [2, 3], [3, 4], [0, 5], [5, 6], [6, 7], [7, 8],
    [5, 9], [9, 10], [10, 11], [11, 12], [9, 13], [13, 14], [14, 15], [15, 16],
    [13, 17], [0, 17], [17, 18], [18, 19], [19, 20]
];

function resize() {
    const viewportWidth = Math.round(window.visualViewport?.width || window.innerWidth);
    const viewportHeight = Math.round(window.visualViewport?.height || window.innerHeight);
    canvas.width = viewportWidth;
    canvas.height = viewportHeight;
    canvas.style.width = `${viewportWidth}px`;
    canvas.style.height = `${viewportHeight}px`;
}
window.addEventListener("resize", resize);
window.visualViewport?.addEventListener("resize", resize);
resize();

function clamp(value, min, max) {
    return Math.min(max, Math.max(min, value));
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
        smoothedHands = [];
        return;
    }
    if (smoothedHands.length !== handLandmarks.length) {
        smoothedHands = handLandmarks.map(hand => hand.map(pt => ({...pt})));
        return;
    }
    smoothedHands = handLandmarks.map((hand, handIndex) => {
        const previousHand = smoothedHands[handIndex];
        return hand.map((point, pointIndex) => smoothPoint(previousHand[pointIndex], point, 0.6));
    });
}

function isFingerUp(hand, tipIndex, pipIndex) { return hand[tipIndex].y < hand[pipIndex].y; }
function isThumbUp(hand) { return Math.abs(hand[4].x - hand[3].x) > 0.03; }

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
    if (distThumbIndex < 0.05 && middle && ring && pinky) return "OK 👌";
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

async function startCamera() {
    try {
        const videoConstraints = isMobile
            ? { facingMode: { ideal: "user" }, width: { ideal: 960, max: 1280 }, height: { ideal: 540, max: 720 } }
            : { facingMode: "user", width: { ideal: 1280 }, height: { ideal: 720 } };
        const stream = await navigator.mediaDevices.getUserMedia({ video: videoConstraints, audio: false });
        video.srcObject = stream; await video.play(); drawScene(); detectLoop();
    } catch (err) { info.innerText = "Không mở được camera: " + err.message; }
}

const hands = new Hands({ locateFile: f => `https://cdn.jsdelivr.net/npm/@mediapipe/hands/${f}` });
hands.setOptions({ maxNumHands: 2, modelComplexity: 1, minDetectionConfidence: 0.6, minTrackingConfidence: 0.6, selfieMode: true });
hands.onResults(res => { 
    latestHandResult = res; 
    updateSmoothedHands(res.multiHandLandmarks || []); 
});

const faceMesh = new FaceMesh({ locateFile: f => `https://cdn.jsdelivr.net/npm/@mediapipe/face_mesh/${f}` });
faceMesh.setOptions({ maxNumFaces: 1, refineLandmarks: true, minDetectionConfidence: 0.5, minTrackingConfidence: 0.5, selfieMode: true });
faceMesh.onResults(res => { latestFaceResult = res; });

function drawScene() {
    if (video.readyState >= 2) {
        const rect = getDrawRect();
        const uiScale = getUiScale();
        const baseLabelFont = Math.round(16 * uiScale);
        const gestureFont = Math.round(26 * uiScale);
        const statusFont = Math.round(26 * uiScale);
        const handLineWidth = clamp(5 * uiScale, 3, 5);
        const pointRadius = clamp(5 * uiScale, 3, 5);
        const strokeThin = clamp(1.5 * uiScale, 1.1, 1.5);
        const safeMargin = Math.round(clamp(canvas.width * 0.02, 12, 24));
        ctx.clearRect(0, 0, canvas.width, canvas.height);
        ctx.save(); ctx.translate(rect.offsetX + rect.drawWidth, rect.offsetY); ctx.scale(-1, 1);
        ctx.drawImage(video, 0, 0, rect.drawWidth, rect.drawHeight); ctx.restore();

        let faceFound = false;
        if (latestFaceResult?.multiFaceLandmarks?.length > 0) {
            faceFound = true; const face = latestFaceResult.multiFaceLandmarks[0];
            ctx.strokeStyle = "#00bfff"; ctx.lineWidth = strokeThin; ctx.beginPath();
            const oval = [10, 338, 297, 332, 284, 251, 389, 356, 454, 323, 361, 288, 397, 365, 379, 378, 400, 377, 152, 148, 176, 149, 150, 136, 172, 58, 132, 93, 234, 127, 162, 21, 54, 103, 67, 109, 10];
            for(let i=0; i < oval.length; i++) { const pt = mapPoint(face[oval[i]], rect); if(i===0) ctx.moveTo(pt.x, pt.y); else ctx.lineTo(pt.x, pt.y); }
            ctx.stroke();
            const avgEAR = (calculateEAR([33, 160, 158, 133, 153, 144], face) + calculateEAR([362, 385, 387, 263, 373, 380], face)) / 2.0;
            if (avgEAR < EAR_THRESHOLD) { eyeClosedFrames++; isSleeping = eyeClosedFrames >= CLOSED_FRAMES_THRESHOLD; faceStatus = isSleeping ? "BUỒN NGỦ!" : "Đang nhắm mắt..."; }
            else { eyeClosedFrames = 0; faceStatus = "Tỉnh táo"; isSleeping = false; }
        }

        if (isSleeping) { if (!alarmInterval) { playBeep(); alarmInterval = setInterval(playBeep, 400); } }
        else { if (alarmInterval) { clearInterval(alarmInterval); alarmInterval = null; } }

        let facesToDraw = [];
        const cx = canvas.width / 2; const cy = canvas.height / 2;

        if (boxes3D.length > 0) {
            boxes3D.forEach(b => {
                let vertices = [{x:-1,y:-1,z:-1},{x:1,y:-1,z:-1},{x:1,y:1,z:-1},{x:-1,y:1,z:-1},{x:-1,y:-1,z:1},{x:1,y:-1,z:1},{x:1,y:1,z:1},{x:-1,y:1,z:1}];
                let projected = vertices.map(v => {
                    let vx = (v.x * BOX_SIZE/2) + (b.gridX - cx);
                    let vy = (v.y * BOX_SIZE/2) + (b.gridY - cy);
                    let vz = (v.z * BOX_SIZE/2) + (b.z);
                    let tx = vx * Math.cos(rotationAngle) - vz * Math.sin(rotationAngle);
                    let tz = vx * Math.sin(rotationAngle) + vz * Math.cos(rotationAngle);
                    vx = tx; vz = tz;
                    let ty = vy * Math.cos(rotationAngleY) - vz * Math.sin(rotationAngleY);
                    vz = vy * Math.sin(rotationAngleY) + vz * Math.cos(rotationAngleY);
                    vy = ty;
                    return { x: vx + cx, y: vy + cy, z: vz };
                });
                let boxFaces = [{i:[0,1,2,3],c:"#1976D2"},{i:[4,5,6,7],c:"#42A5F5"},{i:[0,1,5,4],c:"#90CAF9"},{i:[2,3,7,6],c:"#0D47A1"},{i:[0,3,7,4],c:"#1E88E5"},{i:[1,2,6,5],c:"#1565C0"}];
                boxFaces.forEach((f, i) => {
                    f.z = (projected[f.i[0]].z + projected[f.i[1]].z + projected[f.i[2]].z + projected[f.i[3]].z) / 4;
                    f.pts = [projected[f.i[0]], projected[f.i[1]], projected[f.i[2]], projected[f.i[3]]];
                    f.sourceBox = b; f.faceIndex = i; f.color = f.c;
                    facesToDraw.push(f);
                });
            });
        }

        // Vẽ tay bằng dữ liệu đã smooth để đỡ giật
        if (smoothedHands.length > 0) {
            smoothedHands.forEach((hand, handIdx) => {
                const label = latestHandResult?.multiHandedness[handIdx]?.label || "Unknown";
                const fingersUp = countRaisedFingers(hand);
                const mappedPoints = hand.map(pt => mapPoint(pt, rect));
                const wrist = mappedPoints[0];
                const labelOffsetX = Math.round(15 * uiScale);
                const labelOffsetY = Math.round(15 * uiScale);

                ctx.fillStyle = "#ffffff"; ctx.font = `bold ${baseLabelFont}px sans-serif`;
                ctx.fillText(`Tay ${handIdx + 1} (${label}) | ${fingersUp} ngón`, wrist.x + labelOffsetX, wrist.y - labelOffsetY);

                if (label === "Left") {
                    if (fingersUp === 5) boxes3D = [];
                    if (fingersUp === 1) lightOn = true; else if (fingersUp === 0) lightOn = false;
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
                    if (distPinch < 0.05) {
                        const mx = (mappedPoints[4].x + mappedPoints[8].x) / 2, my = (mappedPoints[4].y + mappedPoints[8].y) / 2;
                        let hit = null;
                        let sortedFaces = [...facesToDraw].sort((a,b) => b.z - a.z);
                        sortedFaces.forEach(f => {
                            ctx.beginPath(); ctx.moveTo(f.pts[0].x, f.pts[0].y); ctx.lineTo(f.pts[1].x, f.pts[1].y); ctx.lineTo(f.pts[2].x, f.pts[2].y); ctx.lineTo(f.pts[3].x, f.pts[3].y); ctx.closePath();
                            if (ctx.isPointInPath(mx, my)) hit = f;
                        });
                        if (!hit && performance.now() - lastBoxTime > 150) {
                            const gx = Math.round(mx / BOX_SIZE) * BOX_SIZE, gy = Math.round(my / BOX_SIZE) * BOX_SIZE;
                            if (!boxes3D.find(b => b.gridX === gx && b.gridY === gy)) { boxes3D.push({ gridX: gx, gridY: gy, z: 0, faceDrawings: Array(6).fill().map(() => []) }); lastBoxTime = performance.now(); }
                        }
                    }
                }

                ctx.strokeStyle = "rgba(0, 255, 250, 0.8)"; ctx.lineWidth = handLineWidth; ctx.lineCap = "round"; ctx.beginPath();
                HAND_CONNECTIONS.forEach(([s, e]) => { ctx.moveTo(mappedPoints[s].x, mappedPoints[s].y); ctx.lineTo(mappedPoints[e].x, mappedPoints[e].y); });
                ctx.stroke();
                ctx.fillStyle = "#FFD700"; mappedPoints.forEach(pt => { ctx.beginPath(); ctx.arc(pt.x, pt.y, pointRadius, 0, 2 * Math.PI); ctx.fill(); });
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
            const glow = ctx.createRadialGradient(cx, cy, Math.round(clamp(40 * uiScale, 24, 40)), cx, cy, Math.max(canvas.width, canvas.height)/1.3);
            glow.addColorStop(0, "rgba(211,255,180,0.3)"); glow.addColorStop(1, "rgba(255,220,80,0)");
            ctx.fillStyle = glow; ctx.fillRect(0, 0, canvas.width, canvas.height);
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
        const now = performance.now(); renderFps = 1000 / (now - lastTime); lastTime = now;     
        info.innerText = `FPS: ${renderFps.toFixed(1)} | Tay: ${smoothedHands.length} | Mặt: ${faceStatus}`;
    }
    requestAnimationFrame(drawScene);
}

async function detectLoop() {
    if (video.readyState >= 2 && !detectBusy) {
        detectBusy = true;
        try { await hands.send({ image: video }); await faceMesh.send({ image: video }); }
        catch(e) { console.error(e); }
        finally { detectBusy = false; }
    }
    requestAnimationFrame(detectLoop);
}
startCamera();
