const video = document.getElementById("video");
const canvas = document.getElementById("canvas");
const ctx = canvas.getContext("2d", { alpha: false });
const info = document.getElementById("info");
const audioBtn = document.getElementById("start-audio-btn");
const isMobile = /Android|webOS|iPhone|iPad|iPod|BlackBerry|IEMobile|Opera Mini/i.test(navigator.userAgent);

let lastTime = performance.now();
let renderFps = 0;
let detectBusy = false;
let latestFaceResult = null;
let smoothedHands = [];
let stableHandedness = [];
let latestHandsRaw = [];
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
let lastRenderAt = 0;

const PERF = {
    detectIntervalMs: isMobile ? 32 : 24,
    renderIntervalMs: isMobile ? 36 : 33,
    renderScale: isMobile ? 0.88 : 0.94,
    maxBoxes: isMobile ? 20 : 56,
    handModelComplexity: isMobile ? 0 : 1,
    faceRefineLandmarks: false,
    pinchHitTestMs: isMobile ? 56 : 24,
    infoRefreshMs: 120,
    handHoldMs: 180,
    faceHoldMs: 280
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

const HAND_CONNECTIONS = [
    [0, 1], [1, 2], [2, 3], [3, 4],
    [0, 5], [5, 6], [6, 7], [7, 8],
    [5, 9], [9, 10], [10, 11], [11, 12],
    [9, 13], [13, 14], [14, 15], [15, 16],
    [13, 17], [17, 18], [18, 19], [19, 20],
    [0, 17]
];

const FACE_OVAL_INDICES = [
    10, 338, 297, 332, 284, 251, 389, 356, 454, 323, 361, 288,
    397, 365, 379, 378, 400, 377, 152, 148, 176, 149, 150, 136,
    172, 58, 132, 93, 234, 127, 162, 21, 54, 103, 67, 109
];

// State cho khối 3D
let boxes3D = [];
let rotationAngle = 0;
let rotationAngleY = 0; 
let lastBoxTime = 0;
const BOX_SIZE = 40;
const BOX_ADD_COOLDOWN_MS = 85;
let wasZeroFingers = false;
let lastHandX = 0;
let lastHandY = 0; 
let pinchActive = false;
let rightMode = "idle";
let rightModeCandidate = "idle";
let rightModeCandidateFrames = 0;
let lastPinchPoint = null;
let leftFingerCandidate = null;
let leftFingerStableFrames = 0;
let leftFingerStable = null;
let leftGestureCandidate = null;
let leftGestureStableFrames = 0;
let leftGestureStable = null;
let leftGestureLastSeenAt = 0;
let lastLeftClearAt = 0;
let handSideTracks = {
    Left: { wrist: null, seenAt: 0 },
    Right: { wrist: null, seenAt: 0 }
};
let singleHandLockLabel = null;
let singleHandLockLastSeenAt = 0;
const LEFT_ACTION_STABLE_FRAMES = 3;
const LEFT_CLEAR_COOLDOWN_MS = 900;
const GESTURE_STABLE_FRAMES = 2;
const GESTURE_HOLD_MS = 220;
const SIDE_TRACK_TIMEOUT_MS = 700;
const SINGLE_HAND_LOCK_TIMEOUT_MS = 2500;
const HAND_LABEL_CONFIDENCE = 0.7;
const HAND_DUPLICATE_DISTANCE = 0.075;
const RIGHT_MODE_STABLE_FRAMES = 3;
const PINCH_MOVE_MIN = 0.015;
const FINGER_UP_TOLERANCE = 0.045;
const THUMB_EXTENSION_ANGLE_DEG = 150;
const THUMB_OPEN_DISTANCE_MIN = 0.095;
const THUMB_TO_INDEX_MCP_MIN = 0.07;
const THUMB_TO_PALM_CENTER_MIN = 0.08;
const THUMB_SEGMENT_DELTA_MIN = 0.015;
const FINGER_CURL_TOLERANCE = 0.012;
const FIST_CURL_MIN_FINGERS = 3;
const FIST_FINGER_TO_PALM_RATIO = 1.05;
const FIST_THUMB_TO_PALM_RATIO = 0.85;
const PINCH_DISTANCE_THRESHOLD = 0.095;
const PINCH_RELEASE_DISTANCE_THRESHOLD = 0.125;
const ROTATE_ENTRY_PINCH_DISTANCE = 0.16;
const STRONG_PINCH_DISTANCE_THRESHOLD = 0.072;
const OK_GESTURE_DISTANCE_THRESHOLD = 0.095;
const ROTATE_DEADZONE = 0.0015;
const ROTATION_SENSITIVITY = 5.8;

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
    const renderWidth = Math.max(320, Math.round(viewportWidth * PERF.renderScale));
    const renderHeight = Math.max(180, Math.round(viewportHeight * PERF.renderScale));
    if (canvas.width === renderWidth && canvas.height === renderHeight) return;
    canvas.width = renderWidth;
    canvas.height = renderHeight;
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

function getPointDistance(a, b) {
    if (!a || !b) return Infinity;
    return Math.hypot(a.x - b.x, a.y - b.y);
}

function isPointInTriangle(px, py, ax, ay, bx, by, cx, cy) {
    const v0x = cx - ax;
    const v0y = cy - ay;
    const v1x = bx - ax;
    const v1y = by - ay;
    const v2x = px - ax;
    const v2y = py - ay;
    const dot00 = v0x * v0x + v0y * v0y;
    const dot01 = v0x * v1x + v0y * v1y;
    const dot02 = v0x * v2x + v0y * v2y;
    const dot11 = v1x * v1x + v1y * v1y;
    const dot12 = v1x * v2x + v1y * v2y;
    const denom = (dot00 * dot11 - dot01 * dot01);
    if (Math.abs(denom) < 1e-8) return false;
    const inv = 1 / denom;
    const u = (dot11 * dot02 - dot01 * dot12) * inv;
    const v = (dot00 * dot12 - dot01 * dot02) * inv;
    return u >= 0 && v >= 0 && (u + v) <= 1;
}

function isPointInQuad(px, py, quad) {
    const a = quad[0], b = quad[1], c = quad[2], d = quad[3];
    return isPointInTriangle(px, py, a.x, a.y, b.x, b.y, c.x, c.y) ||
        isPointInTriangle(px, py, a.x, a.y, c.x, c.y, d.x, d.y);
}

function sanitizeHandDetections(handLandmarks, handedness = []) {
    if (!handLandmarks || handLandmarks.length === 0) return { hands: [], handedness: [] };
    const pairs = handLandmarks.map((hand, idx) => ({
        hand: hand.map(pt => ({ ...pt })),
        handedness: handedness[idx] || null,
        score: Number.isFinite(handedness[idx]?.score) ? handedness[idx].score : 0
    }));

    pairs.sort((a, b) => b.score - a.score);

    const kept = [];
    for (let i = 0; i < pairs.length; i++) {
        const candidate = pairs[i];
        const isDuplicate = kept.some(existing =>
            getPointDistance(existing.hand[0], candidate.hand[0]) < HAND_DUPLICATE_DISTANCE
        );
        if (!isDuplicate) kept.push(candidate);
    }

    kept.sort((a, b) => a.hand[0].x - b.hand[0].x);

    return {
        hands: kept.map(item => item.hand),
        handedness: kept.map(item => item.handedness)
    };
}

function resetRightInteraction(cx = null, cy = null, commitRotation = false) {
    if (commitRotation && rightMode === "rotate" && wasZeroFingers && Number.isFinite(cx) && Number.isFinite(cy)) {
        commitRotationToBoxes(cx, cy);
        rotationAngle = 0;
        rotationAngleY = 0;
    }
    rightMode = "idle";
    rightModeCandidate = "idle";
    rightModeCandidateFrames = 0;
    pinchActive = false;
    wasZeroFingers = false;
    lastPinchPoint = null;
}

function resolveStableHandSides(hands, handedness = []) {
    const now = performance.now();
    const result = hands.map(() => ({ label: null, score: 1 }));
    if (hands.length === 0) return result;

    const raw = hands.map((_, idx) => {
        const h = handedness[idx];
        return {
            label: (h?.label === "Left" || h?.label === "Right") ? h.label : null,
            score: Number.isFinite(h?.score) ? h.score : 0
        };
    });

    if (hands.length === 1) {
        const wrist = hands[0][0];
        const lockAlive = singleHandLockLabel &&
            (now - singleHandLockLastSeenAt) <= SINGLE_HAND_LOCK_TIMEOUT_MS;

        let label = lockAlive ? singleHandLockLabel : null;
        if (!label) {
            const leftTrack = handSideTracks.Left;
            const rightTrack = handSideTracks.Right;
            const leftRecent = leftTrack.wrist && (now - leftTrack.seenAt) <= SIDE_TRACK_TIMEOUT_MS;
            const rightRecent = rightTrack.wrist && (now - rightTrack.seenAt) <= SIDE_TRACK_TIMEOUT_MS;
            if (leftRecent && rightRecent) {
                const dLeft = getPointDistance(wrist, leftTrack.wrist);
                const dRight = getPointDistance(wrist, rightTrack.wrist);
                label = dLeft <= dRight ? "Left" : "Right";
            } else if (raw[0].label && raw[0].score >= HAND_LABEL_CONFIDENCE) {
                label = raw[0].label;
            } else {
                label = wrist.x < 0.5 ? "Left" : "Right";
            }
        }

        result[0] = { label, score: raw[0].score || 0.5 };
        handSideTracks[label] = { wrist: { x: wrist.x, y: wrist.y }, seenAt: now };
        singleHandLockLabel = label;
        singleHandLockLastSeenAt = now;
        return result;
    }

    const takenDetections = new Set();
    const takenLabels = new Set();

    // Step 1: trust confident handedness labels first.
    ["Left", "Right"].forEach(label => {
        let bestIdx = -1;
        let bestScore = -1;
        for (let i = 0; i < raw.length; i++) {
            if (takenDetections.has(i)) continue;
            if (raw[i].label !== label) continue;
            if (raw[i].score < HAND_LABEL_CONFIDENCE) continue;
            if (raw[i].score > bestScore) {
                bestScore = raw[i].score;
                bestIdx = i;
            }
        }
        if (bestIdx >= 0) {
            result[bestIdx] = { label, score: bestScore };
            takenDetections.add(bestIdx);
            takenLabels.add(label);
        }
    });

    // Step 2: for remaining hands, attach to nearest recent track.
    for (let i = 0; i < hands.length; i++) {
        if (takenDetections.has(i)) continue;
        let bestLabel = null;
        let bestDist = Infinity;
        ["Left", "Right"].forEach(label => {
            if (takenLabels.has(label)) return;
            const track = handSideTracks[label];
            if (!track.wrist || (now - track.seenAt) > SIDE_TRACK_TIMEOUT_MS) return;
            const dist = getPointDistance(hands[i][0], track.wrist);
            if (dist < bestDist) {
                bestDist = dist;
                bestLabel = label;
            }
        });
        if (bestLabel) {
            result[i] = { label: bestLabel, score: raw[i].score || 0.5 };
            takenDetections.add(i);
            takenLabels.add(bestLabel);
        }
    }

    // Step 3: final fallback by horizontal position for any unresolved labels.
    const remainingIdx = [];
    for (let i = 0; i < hands.length; i++) {
        if (!takenDetections.has(i)) remainingIdx.push(i);
    }
    remainingIdx.sort((a, b) => hands[a][0].x - hands[b][0].x);
    for (let k = 0; k < remainingIdx.length; k++) {
        const i = remainingIdx[k];
        let label;
        if (!takenLabels.has("Left")) label = "Left";
        else if (!takenLabels.has("Right")) label = "Right";
        else {
            label = k === 0 ? "Left" : "Right";
        }
        result[i] = { label, score: raw[i].score || 0.5 };
        takenLabels.add(label);
    }

    // Step 4: update per-side tracks from resolved labels.
    for (let i = 0; i < hands.length; i++) {
        const label = result[i].label;
        if (!label) continue;
        handSideTracks[label] = {
            wrist: { x: hands[i][0].x, y: hands[i][0].y },
            seenAt: now
        };
        if (singleHandLockLabel === label) {
            singleHandLockLastSeenAt = now;
        }
    }

    return result;
}

function pickBestPreviousHand(currentHand, previousHands, usedPrevious) {
    let bestIndex = -1;
    let bestDist = Infinity;
    for (let i = 0; i < previousHands.length; i++) {
        if (usedPrevious.has(i)) continue;
        const prevWrist = previousHands[i][0];
        const currWrist = currentHand[0];
        const dist = Math.hypot(prevWrist.x - currWrist.x, prevWrist.y - currWrist.y);
        if (dist < bestDist) {
            bestDist = dist;
            bestIndex = i;
        }
    }
    if (bestIndex >= 0) usedPrevious.add(bestIndex);
    return bestIndex;
}

function getAdaptiveHandSmoothingAlpha(prevHand, currentHand) {
    if (!prevHand || !currentHand) return 0;
    const wristDist = getPointDistance(prevHand[0], currentHand[0]);
    if (!Number.isFinite(wristDist) || wristDist > 0.22) return 0;
    if (wristDist > 0.12) return 0.08;
    if (wristDist > 0.06) return 0.14;
    return 0.2;
}

function updateSmoothedHands(handLandmarks, handedness = []) {
    const sanitized = sanitizeHandDetections(handLandmarks, handedness);
    const currentHandsRaw = sanitized.hands;
    const currentHandedness = sanitized.handedness;

    if (currentHandsRaw.length === 0) {
        if (handsMissingSince === null) handsMissingSince = performance.now();
        if (performance.now() - handsMissingSince > PERF.handHoldMs) {
            smoothedHands = [];
            stableHandedness = [];
            latestHandsRaw = [];
            leftFingerCandidate = null;
            leftFingerStableFrames = 0;
            leftFingerStable = null;
            leftGestureCandidate = null;
            leftGestureStableFrames = 0;
            leftGestureStable = null;
            leftGestureLastSeenAt = 0;
            resetRightInteraction();
            singleHandLockLabel = null;
            singleHandLockLastSeenAt = 0;
        }
        return;
    }
    handsMissingSince = null;
    const currentHands = currentHandsRaw;
    const currentResolvedSides = resolveStableHandSides(currentHands, currentHandedness);
    const previousHands = smoothedHands;
    const usedPrevious = new Set();
    const prevByLabel = {};
    for (let i = 0; i < stableHandedness.length; i++) {
        const label = stableHandedness[i]?.label;
        if (!label || prevByLabel[label] !== undefined) continue;
        prevByLabel[label] = i;
    }

    const previousIndexByCurrent = currentHands.map((hand, handIndex) => {
        const label = currentResolvedSides[handIndex]?.label;
        if (label && prevByLabel[label] !== undefined && !usedPrevious.has(prevByLabel[label])) {
            usedPrevious.add(prevByLabel[label]);
            return prevByLabel[label];
        }
        return pickBestPreviousHand(hand, previousHands, usedPrevious);
    });

    smoothedHands = currentHands.map((hand, handIndex) => {
        const prevIdx = previousIndexByCurrent[handIndex];
        const previousHand = prevIdx >= 0 ? previousHands[prevIdx] : null;
        const alpha = getAdaptiveHandSmoothingAlpha(previousHand, hand);
        if (alpha === 0 || !previousHand) {
            return hand.map(point => ({ x: point.x, y: point.y, z: point.z || 0 }));
        }
        return hand.map((point, pointIndex) => smoothPoint(previousHand?.[pointIndex], point, alpha));
    });

    stableHandedness = currentResolvedSides;
    latestHandsRaw = currentHands.map(hand => hand.map(point => ({ x: point.x, y: point.y, z: point.z || 0 })));
}

function isFingerUp(hand, tipIndex, pipIndex) { return hand[tipIndex].y < (hand[pipIndex].y + FINGER_UP_TOLERANCE); }
function isFingerCurled(hand, tipIndex, pipIndex) { return hand[tipIndex].y > (hand[pipIndex].y + FINGER_CURL_TOLERANCE); }

function getPalmCenter(hand) {
    return {
        x: (hand[0].x + hand[5].x + hand[9].x + hand[13].x + hand[17].x) / 5,
        y: (hand[0].y + hand[5].y + hand[9].y + hand[13].y + hand[17].y) / 5
    };
}

function getPalmWidth(hand) {
    return Math.hypot(hand[5].x - hand[17].x, hand[5].y - hand[17].y);
}

function getAngleDeg(a, b, c) {
    const bax = a.x - b.x;
    const bay = a.y - b.y;
    const baz = (a.z || 0) - (b.z || 0);
    const bcx = c.x - b.x;
    const bcy = c.y - b.y;
    const bcz = (c.z || 0) - (b.z || 0);
    const dot = bax * bcx + bay * bcy + baz * bcz;
    const magBA = Math.hypot(bax, bay, baz);
    const magBC = Math.hypot(bcx, bcy, bcz);
    if (magBA < 1e-6 || magBC < 1e-6) return 0;
    const cosTheta = clamp(dot / (magBA * magBC), -1, 1);
    return Math.acos(cosTheta) * (180 / Math.PI);
}

function isThumbUp(hand) {
    const angle = getAngleDeg(hand[2], hand[3], hand[4]);
    const openDistance = Math.hypot(hand[4].x - hand[2].x, hand[4].y - hand[2].y);
    const prevSegment = Math.hypot(hand[3].x - hand[2].x, hand[3].y - hand[2].y);
    const thumbToIndexMcp = Math.hypot(hand[4].x - hand[5].x, hand[4].y - hand[5].y);
    const palmCenter = getPalmCenter(hand);
    const thumbToPalmCenter = Math.hypot(hand[4].x - palmCenter.x, hand[4].y - palmCenter.y);
    return angle >= THUMB_EXTENSION_ANGLE_DEG &&
        openDistance >= THUMB_OPEN_DISTANCE_MIN &&
        (openDistance - prevSegment) >= THUMB_SEGMENT_DELTA_MIN &&
        thumbToIndexMcp >= THUMB_TO_INDEX_MCP_MIN &&
        thumbToPalmCenter >= THUMB_TO_PALM_CENTER_MIN;
}

function isFistPose(hand) {
    const palmCenter = getPalmCenter(hand);
    const palmWidth = Math.max(getPalmWidth(hand), 0.02);
    const fingerToPalmMax = palmWidth * FIST_FINGER_TO_PALM_RATIO;
    const thumbToPalmMax = palmWidth * FIST_THUMB_TO_PALM_RATIO;

    const curledCount =
        (isFingerCurled(hand, 8, 6) ? 1 : 0) +
        (isFingerCurled(hand, 12, 10) ? 1 : 0) +
        (isFingerCurled(hand, 16, 14) ? 1 : 0) +
        (isFingerCurled(hand, 20, 18) ? 1 : 0);

    const indexToPalm = getPointDistance(hand[8], palmCenter);
    const middleToPalm = getPointDistance(hand[12], palmCenter);
    const ringToPalm = getPointDistance(hand[16], palmCenter);
    const pinkyToPalm = getPointDistance(hand[20], palmCenter);
    const thumbToPalm = getPointDistance(hand[4], palmCenter);

    const fingersNearPalm =
        indexToPalm <= fingerToPalmMax &&
        middleToPalm <= fingerToPalmMax &&
        ringToPalm <= fingerToPalmMax &&
        pinkyToPalm <= fingerToPalmMax;

    const thumbFolded = thumbToPalm <= thumbToPalmMax || !isThumbUp(hand);

    return curledCount >= FIST_CURL_MIN_FINGERS && fingersNearPalm && thumbFolded;
}

function isPinchPose(hand, distThreshold) {
    const distPinch = Math.hypot(hand[4].x - hand[8].x, hand[4].y - hand[8].y);
    return distPinch < distThreshold;
}

function getAdaptivePinchThreshold(hand) {
    const palmWidth = Math.max(getPalmWidth(hand), 0.035);
    return {
        enter: clamp(palmWidth * 0.72, 0.055, PINCH_DISTANCE_THRESHOLD),
        release: clamp(palmWidth * 0.95, 0.07, PINCH_RELEASE_DISTANCE_THRESHOLD),
        strong: clamp(palmWidth * 0.58, 0.045, STRONG_PINCH_DISTANCE_THRESHOLD)
    };
}

function countRaisedFingers(hand) {
    let count = 0;
    if (isThumbUp(hand)) count++;
    if (isFingerUp(hand, 8, 6)) count++;
    if (isFingerUp(hand, 12, 10)) count++;
    if (isFingerUp(hand, 16, 14)) count++;
    if (isFingerUp(hand, 20, 18)) count++;
    return count;
}

function updateStableValue(rawValue, candidate, stableFrames, stableValue, requiredFrames) {
    if (rawValue === candidate) stableFrames++;
    else {
        candidate = rawValue;
        stableFrames = 1;
    }
    if (stableFrames >= requiredFrames) stableValue = candidate;
    return { candidate, stableFrames, stableValue };
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

function commitRotationToBoxes(cx, cy) {
    boxes3D.forEach(b => {
        let vx = b.gridX - cx;
        let vy = b.gridY - cy;
        let vz = b.z || 0;
        let tx = vx * Math.cos(rotationAngle) - vz * Math.sin(rotationAngle);
        let tz = vx * Math.sin(rotationAngle) + vz * Math.cos(rotationAngle);
        vx = tx;
        vz = tz;
        let ty = vy * Math.cos(rotationAngleY) - vz * Math.sin(rotationAngleY);
        vz = vy * Math.sin(rotationAngleY) + vz * Math.cos(rotationAngleY);
        vy = ty;
        b.gridX = vx + cx;
        b.gridY = vy + cy;
        b.z = vz;
    });
}

function getDistance(p1, p2) { return Math.sqrt(Math.pow(p1.x - p2.x, 2) + Math.pow(p1.y - p2.y, 2)); }

function calculateEAR(eyeIdx, face) {
    const p1 = face[eyeIdx[0]], p2 = face[eyeIdx[1]], p3 = face[eyeIdx[2]], p4 = face[eyeIdx[3]], p5 = face[eyeIdx[4]], p6 = face[eyeIdx[5]];
    const v1 = getDistance(p2, p6), v2 = getDistance(p3, p5), h = getDistance(p1, p4);
    return (v1 + v2) / (2.0 * h);
}

function scheduleDraw() {
    if (typeof video.requestVideoFrameCallback === "function") {
        video.requestVideoFrameCallback(() => {
            const now = performance.now();
            if ((now - lastRenderAt) >= PERF.renderIntervalMs) {
                lastRenderAt = now;
                drawScene();
            }
            scheduleDraw();
        });
    } else {
        requestAnimationFrame(() => {
            const now = performance.now();
            if ((now - lastRenderAt) >= PERF.renderIntervalMs) {
                lastRenderAt = now;
                drawScene();
            }
            scheduleDraw();
        });
    }
}

async function startCamera() {
    try {
        const videoConstraints = isMobile
            ? { facingMode: { ideal: "user" }, width: { ideal: 640, max: 720 }, height: { ideal: 360, max: 480 } }
            : { facingMode: "user", width: { ideal: 960, max: 1280 }, height: { ideal: 540, max: 720 } };
        const stream = await navigator.mediaDevices.getUserMedia({ video: videoConstraints, audio: false });
        video.srcObject = stream; await video.play(); scheduleDraw(); detectLoop();
    } catch (err) { info.innerText = "Không mở được camera: " + err.message; }
}

const hands = new Hands({ locateFile: f => `https://cdn.jsdelivr.net/npm/@mediapipe/hands/${f}` });
hands.setOptions({
    maxNumHands: 2,
    modelComplexity: PERF.handModelComplexity,
    minDetectionConfidence: 0.6,
    minTrackingConfidence: 0.65,
    selfieMode: true
});
hands.onResults(res => { 
    updateSmoothedHands(res.multiHandLandmarks || [], res.multiHandedness || []); 
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
    const now = performance.now();
    const cx = canvas.width / 2;
    const cy = canvas.height / 2;

    ctx.clearRect(0, 0, canvas.width, canvas.height);
    ctx.save();
    ctx.translate(rect.offsetX + rect.drawWidth, rect.offsetY);
    ctx.scale(-1, 1);
    ctx.drawImage(video, 0, 0, rect.drawWidth, rect.drawHeight);
    ctx.restore();

    let faceFound = false;
    const face = latestFaceResult?.multiFaceLandmarks?.[0] || ((now - lastFaceSeenAt) <= PERF.faceHoldMs ? lastFaceLandmarks : null);
    if (face) {
        faceFound = true;
        const avgEARRaw = (calculateEAR([33, 160, 158, 133, 153, 144], face) + calculateEAR([362, 385, 387, 263, 373, 380], face)) / 2.0;
        if (Number.isFinite(avgEARRaw) && avgEARRaw > 0) {
            smoothedEAR = smoothedEAR === null ? avgEARRaw : (smoothedEAR * 0.75 + avgEARRaw * 0.25);
            if (earBaseline === null) earBaseline = smoothedEAR;
            else {
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
                    } else faceStatus = "BUỒN NGỦ!";
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
                } else faceStatus = "BUỒN NGỦ!";
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
            } else faceStatus = "BUỒN NGỦ!";
        } else {
            eyeOpenSince = null;
            faceStatus = "Đang theo dõi mặt...";
        }
    }

    if (isSleeping) {
        if (!alarmInterval) {
            playBeep();
            alarmInterval = setInterval(playBeep, 400);
        }
    } else if (alarmInterval) {
        clearInterval(alarmInterval);
        alarmInterval = null;
    }

    const facesToDraw = [];
    const cosX = Math.cos(rotationAngle);
    const sinX = Math.sin(rotationAngle);
    const cosY = Math.cos(rotationAngleY);
    const sinY = Math.sin(rotationAngleY);

    if (boxes3D.length > 0) {
        boxes3D.forEach(box => {
            const projected = BOX_VERTICES.map(v => {
                let vx = (v.x * BOX_SIZE / 2) + (box.gridX - cx);
                let vy = (v.y * BOX_SIZE / 2) + (box.gridY - cy);
                let vz = (v.z * BOX_SIZE / 2) + box.z;
                const tx = vx * cosX - vz * sinX;
                const tz = vx * sinX + vz * cosX;
                vx = tx;
                vz = tz;
                const ty = vy * cosY - vz * sinY;
                vz = vy * sinY + vz * cosY;
                vy = ty;
                return { x: vx + cx, y: vy + cy, z: vz };
            });

            BOX_FACES.forEach((faceDef, faceIndex) => {
                const p0 = projected[faceDef.i[0]];
                const p1 = projected[faceDef.i[1]];
                const p2 = projected[faceDef.i[2]];
                const p3 = projected[faceDef.i[3]];
                facesToDraw.push({
                    z: (p0.z + p1.z + p2.z + p3.z) / 4,
                    pts: [p0, p1, p2, p3],
                    sourceBox: box,
                    faceIndex,
                    color: faceDef.c,
                    centerX: (p0.x + p1.x + p2.x + p3.x) / 4,
                    centerY: (p0.y + p1.y + p2.y + p3.y) / 4,
                    minX: Math.min(p0.x, p1.x, p2.x, p3.x),
                    maxX: Math.max(p0.x, p1.x, p2.x, p3.x),
                    minY: Math.min(p0.y, p1.y, p2.y, p3.y),
                    maxY: Math.max(p0.y, p1.y, p2.y, p3.y)
                });
            });
        });
    }

    // Xử lý tay 
    if (smoothedHands.length > 0) {
            let rightSeen = false;
            smoothedHands.forEach((hand, handIdx) => {
                const label = stableHandedness[handIdx]?.label || "Unknown";
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
                    const leftGestureState = updateStableValue(
                        gst,
                        leftGestureCandidate,
                        leftGestureStableFrames,
                        leftGestureStable,
                        GESTURE_STABLE_FRAMES
                    );
                    leftGestureCandidate = leftGestureState.candidate;
                    leftGestureStableFrames = leftGestureState.stableFrames;
                    leftGestureStable = leftGestureState.stableValue;
                    if (leftGestureStable) leftGestureLastSeenAt = now;
                    if (leftGestureStable && (now - leftGestureLastSeenAt) <= GESTURE_HOLD_MS) {
                        ctx.fillStyle = "#FFD700";
                        ctx.font = `bold ${gestureFont}px sans-serif`;
                        ctx.fillText(leftGestureStable, wrist.x + labelOffsetX, wrist.y - Math.round(40 * uiScale));
                    }
                }

                if (label === "Right") {
                    rightSeen = true;
                    const distPinch = Math.hypot(hand[4].x - hand[8].x, hand[4].y - hand[8].y);
                    const fistPose = isFistPose(hand);
                    const indexCurled = isFingerCurled(hand, 8, 6);
                    const pinchThreshold = getAdaptivePinchThreshold(hand);
                    const rotatePose = fistPose || fingersUp <= 2 || ((fingersUp === 0) && indexCurled && distPinch > ROTATE_ENTRY_PINCH_DISTANCE);
                    if (fistPose) {
                        pinchActive = false;
                        lastPinchPoint = null;
                        if (rightMode === "pinch") {
                            rightMode = "idle";
                            rightModeCandidate = "idle";
                            rightModeCandidateFrames = RIGHT_MODE_STABLE_FRAMES;
                            wasZeroFingers = false;
                        }
                    }
                    const pinchStrong = isPinchPose(hand, pinchThreshold.strong) && !fistPose;
                    const pinchCandidate = isPinchPose(hand, pinchThreshold.enter) && !fistPose;
                    const pinchStillHeld = pinchActive && isPinchPose(hand, pinchThreshold.release) && !fistPose;
                    let desiredMode = "idle";
                    if (pinchStrong || (pinchActive && pinchStillHeld)) desiredMode = "pinch";
                    else if (rotatePose) desiredMode = "rotate";
                    else if (pinchCandidate) desiredMode = "pinch";

                    if (desiredMode === rightModeCandidate) rightModeCandidateFrames++;
                    else {
                        rightModeCandidate = desiredMode;
                        rightModeCandidateFrames = 1;
                    }

                    if (rightModeCandidateFrames >= RIGHT_MODE_STABLE_FRAMES && rightMode !== rightModeCandidate) {
                        if (rightMode === "rotate" && wasZeroFingers) {
                            commitRotationToBoxes(cx, cy);
                            rotationAngle = 0;
                            rotationAngleY = 0;
                            wasZeroFingers = false;
                        }
                        rightMode = rightModeCandidate;
                        if (rightMode === "rotate") {
                            lastHandX = hand[0].x;
                            lastHandY = hand[0].y;
                            wasZeroFingers = true;
                            pinchActive = false;
                            lastPinchPoint = null;
                        } else if (rightMode === "pinch") {
                            pinchActive = true;
                            wasZeroFingers = false;
                        } else {
                            pinchActive = false;
                            wasZeroFingers = false;
                            lastPinchPoint = null;
                        }
                    }

                    if (rightMode === "rotate") {
                        const dx = hand[0].x - lastHandX;
                        const dy = hand[0].y - lastHandY;
                        if (Math.abs(dx) > ROTATE_DEADZONE) rotationAngle += dx * ROTATION_SENSITIVITY;
                        if (Math.abs(dy) > ROTATE_DEADZONE) rotationAngleY += dy * ROTATION_SENSITIVITY;
                        lastHandX = hand[0].x;
                        lastHandY = hand[0].y;
                    }

                    if (rightMode !== "pinch") {
                        pinchActive = false;
                    }

                    const pinchPointNorm = { x: (hand[4].x + hand[8].x) / 2, y: (hand[4].y + hand[8].y) / 2 };
                    const movedEnough = !lastPinchPoint || Math.hypot(
                        pinchPointNorm.x - lastPinchPoint.x,
                        pinchPointNorm.y - lastPinchPoint.y
                    ) >= PINCH_MOVE_MIN;

                    if (pinchActive && movedEnough && performance.now() - lastPinchHitTestAt >= PERF.pinchHitTestMs) {
                        lastPinchHitTestAt = performance.now();
                        const mx = (mappedPoints[4].x + mappedPoints[8].x) / 2, my = (mappedPoints[4].y + mappedPoints[8].y) / 2;
                        let hit = null;
                        let hitZ = -Infinity;
                        const hitPadding = Math.round(clamp(18 * uiScale, 12, 24));
                        for (let i = 0; i < facesToDraw.length; i++) {
                            const f = facesToDraw[i];
                            if (mx < (f.minX - hitPadding) || mx > (f.maxX + hitPadding) || my < (f.minY - hitPadding) || my > (f.maxY + hitPadding)) continue;
                            if (isPointInQuad(mx, my, f.pts) && f.z > hitZ) {
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
                            const maxFallbackDist = (BOX_SIZE * 2.1) * (BOX_SIZE * 2.1);
                            if (best && bestDist <= maxFallbackDist) hit = best;
                        }
                        if (performance.now() - lastBoxTime > BOX_ADD_COOLDOWN_MS) {
                            if (hit) {
                                const normal = FACE_NORMALS[hit.faceIndex] || { x: 0, y: 0, z: 1 };
                                const nextX = hit.sourceBox.gridX + normal.x * BOX_SIZE;
                                const nextY = hit.sourceBox.gridY + normal.y * BOX_SIZE;
                                const nextZ = (hit.sourceBox.z || 0) + normal.z * BOX_SIZE;
                                if (addBoxAt(nextX, nextY, nextZ)) {
                                    lastPinchPoint = pinchPointNorm;
                                }
                            } else if (boxes3D.length === 0) {
                                const gx = Math.round(mx / BOX_SIZE) * BOX_SIZE;
                                const gy = Math.round(my / BOX_SIZE) * BOX_SIZE;
                                if (addBoxAt(gx, gy, 0)) {
                                    lastPinchPoint = pinchPointNorm;
                                }
                            }
                        }
                    }
                }
            });

        if (!rightSeen) {
            resetRightInteraction(cx, cy, true);
        }
    }

    // Render khối 3D
    if (facesToDraw.length > 0) {
        facesToDraw.sort((a, b) => a.z - b.z);
        facesToDraw.forEach(f => {
            ctx.fillStyle = f.color;
            ctx.strokeStyle = "rgba(255, 255, 255, 0.8)";
            ctx.lineWidth = strokeThin;
            ctx.beginPath();
            ctx.moveTo(f.pts[0].x, f.pts[0].y);
            ctx.lineTo(f.pts[1].x, f.pts[1].y);
            ctx.lineTo(f.pts[2].x, f.pts[2].y);
            ctx.lineTo(f.pts[3].x, f.pts[3].y);
            ctx.closePath();
            ctx.fill();
            ctx.stroke();
        });
    }

    if (lightOn) {
        if (!cachedGlowGradient || cachedGlowWidth !== canvas.width || cachedGlowHeight !== canvas.height) {
            cachedGlowGradient = ctx.createRadialGradient(
                cx,
                cy,
                Math.round(clamp(40 * uiScale, 24, 40)),
                cx,
                cy,
                Math.max(canvas.width, canvas.height) / 1.3
            );
            cachedGlowGradient.addColorStop(0, "rgba(211,255,180,0.3)");
            cachedGlowGradient.addColorStop(1, "rgba(255,220,80,0)");
            cachedGlowWidth = canvas.width;
            cachedGlowHeight = canvas.height;
        }
        ctx.fillStyle = cachedGlowGradient;
        ctx.fillRect(0, 0, canvas.width, canvas.height);
    }

    // Overlay luôn nằm trên cùng để không bị che bởi khối 3D/ánh sáng
    if (face) {
        const mappedFace = face.map(pt => mapPoint(pt, rect));
        const first = mappedFace[FACE_OVAL_INDICES[0]];
        if (first) {
            ctx.strokeStyle = "rgba(0, 255, 200, 0.95)";
            ctx.lineWidth = Math.max(1.3, strokeThin);
            ctx.beginPath();
            ctx.moveTo(first.x, first.y);
            for (let i = 1; i < FACE_OVAL_INDICES.length; i++) {
                const p = mappedFace[FACE_OVAL_INDICES[i]];
                if (p) ctx.lineTo(p.x, p.y);
            }
            ctx.closePath();
            ctx.stroke();
        }
    }

    const handsForOverlay = latestHandsRaw.length > 0 ? latestHandsRaw : smoothedHands;
    if (handsForOverlay.length > 0) {
        const mobileJointIndices = [0, 4, 8, 12, 16, 20];
        handsForOverlay.forEach((hand) => {
            const mappedPoints = hand.map(pt => mapPoint(pt, rect));
            ctx.strokeStyle = "rgba(64, 196, 255, 0.95)";
            ctx.lineWidth = Math.max(1.1, strokeThin);
            for (let i = 0; i < HAND_CONNECTIONS.length; i++) {
                const [a, b] = HAND_CONNECTIONS[i];
                const p1 = mappedPoints[a];
                const p2 = mappedPoints[b];
                if (!p1 || !p2) continue;
                ctx.beginPath();
                ctx.moveTo(p1.x, p1.y);
                ctx.lineTo(p2.x, p2.y);
                ctx.stroke();
            }
            ctx.fillStyle = "rgba(140, 220, 255, 0.95)";
            const jointRadius = Math.max(1.8, 2.8 * uiScale);
            const pointsToDraw = isMobile ? mobileJointIndices : mappedPoints.map((_, idx) => idx);
            for (let i = 0; i < pointsToDraw.length; i++) {
                const p = mappedPoints[pointsToDraw[i]];
                if (!p) continue;
                ctx.beginPath();
                ctx.arc(p.x, p.y, jointRadius, 0, Math.PI * 2);
                ctx.fill();
            }
        });
    }

    ctx.fillStyle = isSleeping ? "#ff3333" : (faceFound ? "#00ffcc" : "#aaaaaa");
    ctx.font = `bold ${statusFont}px sans-serif`;
    ctx.fillText(`Trạng thái: ${faceStatus}`, safeMargin, safeMargin + statusFont);

    if (isSleeping) {
        ctx.fillStyle = "rgba(255, 0, 0, 0.35)";
        ctx.fillRect(0, 0, canvas.width, canvas.height);
        ctx.fillStyle = "#ffffff";
        let warningFont = Math.round(clamp(canvas.width * 0.08, 24, 55));
        const warningText = "⚠️ CẢNH BÁO BUỒN NGỦ ⚠️";
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
                await hands.send({ image: video });
                if (detectPhase === 0) await faceMesh.send({ image: video });
                detectPhase = (detectPhase + 1) % 2;
            } else {
                await hands.send({ image: video });
                if (detectPhase === 0) await faceMesh.send({ image: video });
                detectPhase = (detectPhase + 1) % 2;
            }
        }
        catch(e) { console.error(e); }
        finally { detectBusy = false; }
    }
    const elapsed = performance.now() - now;
    const waitMs = video.readyState >= 2 ? Math.max(12, PERF.detectIntervalMs - elapsed) : 40;
    setTimeout(detectLoop, waitMs);
}
startCamera();
