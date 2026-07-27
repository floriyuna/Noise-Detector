// ============================================================
// KeyNoise Guard — app.js  v3.0
//   ① ハイパスフィルタ 600Hz
//   ② 静寂キャリブレーション (ノイズフロア測定)
//   ③ 打鍵音パターンキャリブレーション (スペクトル指紋学習)
//   ④ 動的キャリブレーションモード
//   ⑤ 入力ゲイン増幅 (マイク遠距離対応)
//   ⑥ キー連動モード (keydown ゲーティング)
//   ⑦ 検知カウンター・ログ強化・CSV出力
//   ⑧ ノイズゲート: 急上昇率チェック [NEW v3]
//   ⑨ ノイズゲート: 持続信号拒否 [NEW v3]
// ============================================================

// ─── Audio nodes ────────────────────────────────────────────
let audioCtx         = null;
let microphoneStream = null;
let sourceNode       = null;
let filterNode       = null;
let gainNode         = null;
let analyserNode     = null;
let animationFrameId = null;

// ─── UI refs ────────────────────────────────────────────────
const startBtn              = document.getElementById('startBtn');
const stopBtn               = document.getElementById('stopBtn');
const statusText            = document.getElementById('statusText');
const statusDot             = document.getElementById('statusDot');
const signalStrengthText    = document.getElementById('signalStrength');
const visualizerCanvas      = document.getElementById('visualizerCanvas');
const canvasCtx             = visualizerCanvas.getContext('2d');

const thresholdRange        = document.getElementById('thresholdRange');
const thresholdValLabel     = document.getElementById('thresholdVal');
const calibModes            = document.getElementsByName('calibMode');

const calibNoiseBtn         = document.getElementById('calibNoiseBtn');
const calibKeyBtn           = document.getElementById('calibKeyBtn');
const noiseFloorStatus      = document.getElementById('noiseFloorStatus');
const keyPatternStatus      = document.getElementById('keyPatternStatus');
const calibrationIndicator  = document.getElementById('calibrationIndicator');
const calibrationStatusText = document.getElementById('calibrationStatusText');

const visualAlertToggle     = document.getElementById('visualAlertToggle');
const audioAlertToggle      = document.getElementById('audioAlertToggle');
const alertOverlay          = document.getElementById('alertOverlay');
const appContainer          = document.getElementById('appContainer');
const logPanel              = document.getElementById('logPanel');
const clearLogBtn           = document.getElementById('clearLogBtn');

// v2 refs
const inputGainRange        = document.getElementById('inputGainRange');
const inputGainValLabel     = document.getElementById('inputGainVal');
const keyTriggerToggle      = document.getElementById('keyTriggerToggle');
const keyTriggerIndicator   = document.getElementById('keyTriggerIndicator');
const keyTriggerStatusEl    = document.getElementById('keyTriggerStatus');
const detectionCountEl      = document.getElementById('detectionCount');
const exportLogBtn          = document.getElementById('exportLogBtn');

// [NEW v3] Noise gate ref
const noiseGateRange        = document.getElementById('noiseGateRange');
const noiseGateValLabel     = document.getElementById('noiseGateVal');

// [NEW v3] Gauge UI refs
const gaugeBarFill          = document.getElementById('gaugeBarFill');
const gaugeThresholdLine    = document.getElementById('gaugeThresholdLine');
const gaugeVal              = document.getElementById('gaugeVal');

// [NEW v4] PiP & Theme refs
const themeToggleBtn        = document.getElementById('themeToggleBtn');
const pipBtn                = document.getElementById('pipBtn');

let pipWindow               = null;
let pipCanvas               = null;
let pipCanvasCtx            = null;
let pipGaugeBarFill         = null;
let pipGaugeVal             = null;
let pipStatusText           = null;
let pipStatusDot            = null;
let pipDetectionCount       = null;
let pipAlertOverlay         = null;


// ─── Runtime state ──────────────────────────────────────────
let isMonitoring       = false;
let calibrationMode    = 'static';
let warningCooldown    = false;

// Envelope follower
let envRMS             = 0.02;

// ─── Calibration data ───────────────────────────────────────
let noiseFloorRMS      = 0.02;
let noiseFloorDone     = false;

let keyboardFingerprint = null;
const NUM_BANDS         = 8;
let keyHitAccum         = [];
let isKeyCalibrating    = false;
let keyCalibCountdown   = 0;
let keyCalibTimer       = null;

let isNoiseCalibrating  = false;
let noiseCalibRMSArr    = [];
let noiseCalibTimer     = null;

let dynamicEnvBaseline  = 0.02;

// ─── Key-trigger mode ────────────────────────────────────────
let keyTriggerMode   = false;
let keyTriggerActive = false;
let keyTriggerTimer  = null;

// ─── Detection counter & log data ───────────────────────────
let sessionDetectionCount = 0;
let logData = [];

// ─── [NEW v3] Noise gate: transient detection state ──────────
//
// Strategy A — 急上昇率ゲート (Rise-rate gate)
//   信号が前フレームから急激に上昇した場合のみ検知を許可する。
//   会話は緩やかに音量が上がるが、打鍵音は1フレームで急上昇する。
//
// Strategy B — 持続信号拒否 (Sustained-signal rejection)
//   信号がしきい値を超えた状態が N フレーム以上連続した場合は
//   「話し声/空調」と判断してブロックする。
//   打鍵音は数フレーム(20-80ms)以内に収まる。
//
let prevSignalRatio            = 0;    // 前フレームのシグナル比率
let consecutiveAboveThresh     = 0;    // しきい値超えの連続フレーム数
const MAX_SUSTAINED_FRAMES     = 5;    // これを超えたら持続音と判定 (~80ms @60fps)

// ─── Canvas resize ──────────────────────────────────────────
function resizeCanvas() {
  visualizerCanvas.width  = visualizerCanvas.parentElement.clientWidth;
  visualizerCanvas.height = 160;
}
window.addEventListener('resize', resizeCanvas);
resizeCanvas();

// ─── Threshold slider ────────────────────────────────────────
thresholdRange.addEventListener('input', e => {
  thresholdValLabel.textContent = parseFloat(e.target.value).toFixed(2);
  updateGaugeThreshold();
});

function getThreshold() { return parseFloat(thresholdRange.value); }

// ─── Input gain slider ───────────────────────────────────────
inputGainRange.addEventListener('input', e => {
  const val = parseFloat(e.target.value);
  inputGainValLabel.textContent = val.toFixed(1) + 'x';
  if (gainNode) gainNode.gain.value = val;
});

function getInputGain() { return parseFloat(inputGainRange.value); }

// ─── [NEW v3] Noise gate slider ──────────────────────────────
noiseGateRange.addEventListener('input', e => {
  noiseGateValLabel.textContent = parseFloat(e.target.value).toFixed(1);
});

function getNoiseGate() { return parseFloat(noiseGateRange.value); }

// ─── Key-trigger toggle ──────────────────────────────────────
keyTriggerToggle.addEventListener('change', e => {
  keyTriggerMode = e.target.checked;
  if (!isMonitoring) return;
  keyTriggerIndicator.style.display = keyTriggerMode ? 'flex' : 'none';
  if (!keyTriggerMode) {
    keyTriggerActive = false;
    clearTimeout(keyTriggerTimer);
  }
});

// Key-trigger: gate audio analysis to 350ms window after keydown
document.addEventListener('keydown', () => {
  if (!keyTriggerMode || !isMonitoring) return;
  keyTriggerActive = true;
  clearTimeout(keyTriggerTimer);
  updateKeyTriggerIndicator(true);
  keyTriggerTimer = setTimeout(() => {
    keyTriggerActive = false;
    updateKeyTriggerIndicator(false);
  }, 350);
});

function updateKeyTriggerIndicator(active) {
  if (active) {
    keyTriggerIndicator.className = 'key-trigger-indicator active';
    keyTriggerStatusEl.textContent = '● キー入力を検知中 — 音声監視中';
  } else {
    keyTriggerIndicator.className = 'key-trigger-indicator';
    keyTriggerStatusEl.textContent = 'キー待機中…';
  }
}

// ─── Calibration mode radio ──────────────────────────────────
calibModes.forEach(r => r.addEventListener('change', e => {
  calibrationMode = e.target.value;
  updateCalibUI();
}));

function updateCalibUI() {
  if (!isMonitoring) {
    calibNoiseBtn.disabled = true;
    calibKeyBtn.disabled   = true;
    calibrationIndicator.className   = 'indicator-dot';
    calibrationStatusText.textContent = '監視開始後にキャリブレーションできます';
    return;
  }
  calibNoiseBtn.disabled = false;
  calibKeyBtn.disabled   = false;

  if (calibrationMode === 'dynamic') {
    calibrationIndicator.className   = 'indicator-dot active';
    calibrationStatusText.textContent = '動的ノイズ追従モード実行中';
  } else {
    const done = noiseFloorDone;
    calibrationIndicator.className   = done ? 'indicator-dot active' : 'indicator-dot';
    calibrationStatusText.textContent = done ? '静的ノイズ基準設定済み' : '静的モード (未キャリブレーション)';
  }
}

// ─── Gauge UI helpers ────────────────────────────────────────
function updateGaugeThreshold() {
  const thresh  = getThreshold();
  const pct     = Math.min(1.0, thresh / 5.0) * 100;
  gaugeThresholdLine.style.bottom = pct + '%';
}

function updateGaugeBar(signalRatio, thresh) {
  const pct     = Math.min(1.0, signalRatio / 5.0) * 100;
  const isAlert = signalRatio > thresh;
  gaugeBarFill.style.height = pct + '%';
  gaugeBarFill.className    = 'gauge-bar-fill' + (isAlert ? ' danger' : '');
  gaugeVal.textContent      = signalRatio.toFixed(1);
  gaugeVal.style.color      = isAlert ? 'var(--clr-danger)' : 'var(--txt-secondary)';

  // [NEW v4] PiP Gauge Sync
  if (pipGaugeBarFill) {
    pipGaugeBarFill.style.height = pct + '%';
    pipGaugeBarFill.className    = 'gauge-bar-fill' + (isAlert ? ' danger' : '');
  }
  if (pipGaugeVal) {
    pipGaugeVal.textContent      = signalRatio.toFixed(1);
    pipGaugeVal.style.color      = isAlert ? 'var(--clr-danger)' : 'var(--txt-secondary)';
  }
}

updateGaugeThreshold();

// ─── START ───────────────────────────────────────────────────
startBtn.addEventListener('click', async () => {
  try {
    microphoneStream = await navigator.mediaDevices.getUserMedia({
      audio: {
        echoCancellation: false,
        noiseSuppression: false,
        autoGainControl: false
      }
    });

    audioCtx   = new (window.AudioContext || window.webkitAudioContext)();
    sourceNode = audioCtx.createMediaStreamSource(microphoneStream);

    // ① Highpass filter 600Hz — voice fundamentals & AC hum cut
    filterNode = audioCtx.createBiquadFilter();
    filterNode.type = 'highpass';
    filterNode.frequency.value = 600;
    filterNode.Q.value = 0.707;

    // ② Input gain — compensates for distant microphone
    gainNode = audioCtx.createGain();
    gainNode.gain.value = getInputGain();

    // ③ Analyser — no temporal smoothing (raw transients)
    analyserNode = audioCtx.createAnalyser();
    analyserNode.fftSize = 1024;
    analyserNode.smoothingTimeConstant = 0.0;

    // Pipeline: mic → HPF → Gain → Analyser
    sourceNode.connect(filterNode);
    filterNode.connect(gainNode);
    gainNode.connect(analyserNode);

    isMonitoring = true;
    startBtn.disabled = true;
    stopBtn.disabled  = false;

    statusText.textContent = '監視中';
    statusText.style.color = 'var(--clr-safe)';
    statusDot.className    = 'status-dot monitoring';

    signalStrengthText.style.color = 'var(--txt-primary)';
    envRMS             = 0.02;
    dynamicEnvBaseline = 0.02;

    // Reset noise gate state
    prevSignalRatio        = 0;
    consecutiveAboveThresh = 0;

    if (keyTriggerMode) {
      keyTriggerIndicator.style.display = 'flex';
    }

    updateCalibUI();
    updateGaugeThreshold();
    drawAndAnalyze();

  } catch (err) {
    console.error('マイクの初期化に失敗しました:', err);
    alert('マイクのアクセス許可が必要です。ブラウザの設定を確認してください。');
  }
});

// ─── STOP ────────────────────────────────────────────────────
stopBtn.addEventListener('click', stopMonitoring);

function stopMonitoring() {
  isMonitoring = false;
  cancelAnimationFrame(animationFrameId);
  clearTimeout(noiseCalibTimer);
  clearTimeout(keyCalibTimer);
  clearTimeout(keyTriggerTimer);
  isNoiseCalibrating = false;
  isKeyCalibrating   = false;
  keyTriggerActive   = false;

  startBtn.disabled = false;
  stopBtn.disabled  = true;

  statusText.textContent = '停止中';
  statusText.style.color = 'var(--txt-secondary)';
  statusDot.className    = 'status-dot';

  signalStrengthText.textContent = '0.00';
  signalStrengthText.style.color = 'var(--txt-secondary)';

  keyTriggerIndicator.style.display = 'none';
  keyTriggerIndicator.className = 'key-trigger-indicator';

  updateGaugeBar(0, getThreshold());

  microphoneStream?.getTracks().forEach(t => t.stop());
  if (audioCtx?.state !== 'closed') audioCtx?.close();
  gainNode = null;

  prevSignalRatio        = 0;
  consecutiveAboveThresh = 0;

  updateCalibUI();
}

// ─── Clear Log ───────────────────────────────────────────────
clearLogBtn.addEventListener('click', () => {
  logPanel.innerHTML = '<div id="logPlaceholder" style="color:var(--txt-muted);text-align:center;padding:24px 0;font-size:0.8rem;">ログはまだありません</div>';
  logData = [];
  sessionDetectionCount = 0;
  if (detectionCountEl) detectionCountEl.textContent = '0';
});

// ─── CSV Export ──────────────────────────────────────────────
exportLogBtn.addEventListener('click', () => {
  if (logData.length === 0) { alert('エクスポートするログがありません。'); return; }
  const bom = '\uFEFF';
  let csv = bom + '時刻,メッセージ,強度,シグナル比率\n';
  logData.forEach(r => { csv += `${r.time},${r.msg},${r.severity},${r.ratio}\n`; });

  const blob = new Blob([csv], { type: 'text/csv;charset=utf-8;' });
  const url  = URL.createObjectURL(blob);
  const a    = document.createElement('a');
  a.href     = url;
  a.download = `keynoise_log_${new Date().toISOString().slice(0,10)}.csv`;
  document.body.appendChild(a);
  a.click();
  document.body.removeChild(a);
  URL.revokeObjectURL(url);
});

// ════════════════════════════════════════════════════════════
// (A) NOISE FLOOR CALIBRATION
// ════════════════════════════════════════════════════════════
calibNoiseBtn.addEventListener('click', () => {
  if (!isMonitoring || isNoiseCalibrating) return;

  isNoiseCalibrating = true;
  noiseCalibRMSArr   = [];
  calibNoiseBtn.disabled = true;
  calibrationIndicator.className   = 'indicator-dot calibrating';
  calibrationStatusText.textContent = '静かにしてください… (3秒測定中)';
  noiseFloorStatus.textContent = '測定中…';

  noiseCalibTimer = setTimeout(() => {
    isNoiseCalibrating = false;
    calibNoiseBtn.disabled = false;
    noiseFloorDone = true;

    if (noiseCalibRMSArr.length > 0) {
      const sorted = [...noiseCalibRMSArr].sort((a, b) => a - b);
      const p95idx = Math.floor(sorted.length * 0.95);
      noiseFloorRMS = sorted[p95idx] || sorted[sorted.length - 1];
      dynamicEnvBaseline = noiseFloorRMS;
      envRMS = noiseFloorRMS;
      noiseFloorStatus.textContent = `完了 (RMS: ${noiseFloorRMS.toFixed(4)})`;
    } else {
      noiseFloorStatus.textContent = '失敗 (データなし)';
    }
    updateCalibUI();
  }, 3000);
});

// ════════════════════════════════════════════════════════════
// (B) KEYBOARD PATTERN CALIBRATION
// ════════════════════════════════════════════════════════════
calibKeyBtn.addEventListener('click', () => {
  if (!isMonitoring || isKeyCalibrating) return;

  isKeyCalibrating  = true;
  keyHitAccum       = [];
  keyCalibCountdown = 10;
  calibKeyBtn.disabled = true;
  calibrationIndicator.className   = 'indicator-dot calibrating';
  calibrationStatusText.textContent = 'キーボードを5回以上叩いてください…';
  keyPatternStatus.textContent = '学習中 (0打鍵)';

  keyCalibTimer = setTimeout(finalizeKeyCalibration, 10000);
});

function collectKeyHit(bandVector) {
  if (!isKeyCalibrating) return;
  keyHitAccum.push(bandVector);
  keyPatternStatus.textContent = `学習中 (${keyHitAccum.length}打鍵)`;
  if (keyHitAccum.length >= 5) {
    clearTimeout(keyCalibTimer);
    finalizeKeyCalibration();
  }
}

function finalizeKeyCalibration() {
  isKeyCalibrating = false;
  calibKeyBtn.disabled = false;

  if (keyHitAccum.length >= 3) {
    keyboardFingerprint = new Float32Array(NUM_BANDS);
    for (const vec of keyHitAccum) {
      for (let b = 0; b < NUM_BANDS; b++) keyboardFingerprint[b] += vec[b];
    }
    for (let b = 0; b < NUM_BANDS; b++) keyboardFingerprint[b] /= keyHitAccum.length;
    const mag = Math.sqrt(keyboardFingerprint.reduce((s, v) => s + v * v, 0)) || 1;
    for (let b = 0; b < NUM_BANDS; b++) keyboardFingerprint[b] /= mag;
    keyPatternStatus.textContent = `学習完了 (${keyHitAccum.length}打鍵)`;
  } else {
    keyboardFingerprint = null;
    keyPatternStatus.textContent = `サンプル不足 (${keyHitAccum.length}打鍵, 3以上必要)`;
  }
  updateCalibUI();
}

// ─── Frequency band energy vector ────────────────────────────
function extractBandVector(freqData) {
  const sampleRate = audioCtx.sampleRate;
  const binCount   = freqData.length;
  const nyquist    = sampleRate / 2;
  const minFreq    = 600;
  const maxFreq    = Math.min(nyquist, 16000);
  const logMin     = Math.log2(minFreq);
  const logMax     = Math.log2(maxFreq);
  const bandVec    = new Float32Array(NUM_BANDS);

  for (let b = 0; b < NUM_BANDS; b++) {
    const fLow    = Math.pow(2, logMin + (b / NUM_BANDS) * (logMax - logMin));
    const fHigh   = Math.pow(2, logMin + ((b + 1) / NUM_BANDS) * (logMax - logMin));
    const binLow  = Math.floor(fLow  / nyquist * binCount);
    const binHigh = Math.ceil (fHigh / nyquist * binCount);
    let sum = 0, count = 0;
    for (let i = binLow; i <= binHigh && i < binCount; i++) { sum += freqData[i]; count++; }
    bandVec[b] = count > 0 ? sum / count / 255.0 : 0;
  }
  return bandVec;
}

// ─── Cosine similarity ────────────────────────────────────────
function cosineSimilarity(a, b) {
  let dot = 0, magA = 0, magB = 0;
  for (let i = 0; i < a.length; i++) {
    dot  += a[i] * b[i];
    magA += a[i] * a[i];
    magB += b[i] * b[i];
  }
  return dot / (Math.sqrt(magA) * Math.sqrt(magB) || 1);
}

// ════════════════════════════════════════════════════════════
// MAIN ANALYSIS LOOP
// ════════════════════════════════════════════════════════════
function drawAndAnalyze() {
  if (!isMonitoring) return;

  const bufferLength = analyserNode.fftSize;
  const timeData     = new Uint8Array(bufferLength);
  analyserNode.getByteTimeDomainData(timeData);

  // ── 1. RMS & peak ──────────────────────────────────────────
  let peak = 0, sumSq = 0;
  for (let i = 0; i < bufferLength; i++) {
    const v = (timeData[i] - 128) / 128;
    const a = Math.abs(v);
    if (a > peak) peak = a;
    sumSq += v * v;
  }
  const rms = Math.sqrt(sumSq / bufferLength);

  if (isNoiseCalibrating) noiseCalibRMSArr.push(rms);

  // ── 2. Envelope follower ────────────────────────────────────
  const alpha = rms > envRMS ? 0.15 : 0.005;
  envRMS = envRMS * (1 - alpha) + rms * alpha;

  if (calibrationMode === 'dynamic') {
    const signalNow = peak / (envRMS + 0.005);
    if (signalNow < getThreshold() * 0.7) {
      dynamicEnvBaseline = dynamicEnvBaseline * 0.998 + envRMS * 0.002;
    }
  }

  // ── 3. Transient ratio ─────────────────────────────────────
  const floorRef    = calibrationMode === 'dynamic' ? dynamicEnvBaseline : noiseFloorRMS;
  const epsilon     = 0.004;
  const signalRatio = peak / (Math.max(floorRef, envRMS * 0.5) + epsilon);

  signalStrengthText.textContent = signalRatio.toFixed(2);

  // ── [NEW v3] Noise gate state tracking ────────────────────
  // 急上昇率 (rise rate): 1フレームでの上昇量
  const riseRate = signalRatio - prevSignalRatio;
  prevSignalRatio = signalRatio;

  // 持続フレームカウント: しきい値の85%以上で連続しているフレーム数
  const thresh = getThreshold();
  if (signalRatio > thresh * 0.85) {
    consecutiveAboveThresh++;
  } else {
    consecutiveAboveThresh = 0;
  }

  // ── 4. Frequency fingerprint ────────────────────────────────
  const freqData       = new Uint8Array(analyserNode.frequencyBinCount);
  analyserNode.getByteFrequencyData(freqData);
  const currentBandVec = extractBandVector(freqData);

  if (isKeyCalibrating && signalRatio > 1.4) collectKeyHit(currentBandVec);

  // ── 5. Detection logic ──────────────────────────────────────
  if (signalRatio > thresh) {
    let shouldAlert = true;

    // Gate A: Key-trigger mode (keydown gating)
    if (keyTriggerMode && !keyTriggerActive) {
      shouldAlert = false;
    }

    // [NEW v3] Gate B: 急上昇率チェック (Rise-rate gate)
    // 話し声は緩やかに上昇する → riseRate が小さい
    // 打鍵音は1フレームで急上昇する → riseRate が大きい
    const noiseGateThresh = getNoiseGate();
    if (shouldAlert && noiseGateThresh > 0 && riseRate < noiseGateThresh) {
      shouldAlert = false;
    }

    // [NEW v3] Gate C: 持続信号拒否 (Sustained-signal rejection)
    // 話し声は何十フレームも続く → consecutiveAboveThresh が増え続ける
    // 打鍵音は数フレームで終わる → 検知直後にリセット
    if (shouldAlert && consecutiveAboveThresh > MAX_SUSTAINED_FRAMES) {
      shouldAlert = false;
    }

    // Gate D: Spectral fingerprint similarity
    if (shouldAlert && keyboardFingerprint !== null) {
      const mag     = Math.sqrt(currentBandVec.reduce((s, v) => s + v * v, 0)) || 1;
      const normVec = currentBandVec.map(v => v / mag);
      const sim     = cosineSimilarity(keyboardFingerprint, normVec);
      shouldAlert   = sim > 0.60;
    }

    if (shouldAlert) triggerAlert(signalRatio);
  }

  // ── 6. Render ───────────────────────────────────────────────
  drawCanvas(timeData, signalRatio, thresh);
  updateGaugeBar(signalRatio, thresh);

  animationFrameId = requestAnimationFrame(drawAndAnalyze);
}

// ─── Alert ───────────────────────────────────────────────────
function triggerAlert(signalVal) {
  if (warningCooldown) return;
  warningCooldown = true;

  // Reset sustained counter so the next keystroke is also detectable
  consecutiveAboveThresh = 0;

  // Increment counter
  sessionDetectionCount++;
  if (detectionCountEl) detectionCountEl.textContent = sessionDetectionCount;
  if (pipDetectionCount) pipDetectionCount.textContent = sessionDetectionCount;

  // Update status + dot
  statusText.textContent = '強打を検知！';
  statusText.style.color = 'var(--clr-danger)';
  if (statusDot) {
    statusDot.className = 'status-dot alert';
  }

  // Update PiP status
  if (pipStatusText) {
    pipStatusText.textContent = '強打を検知！';
    pipStatusText.style.color = 'var(--clr-danger)';
  }
  if (pipStatusDot) {
    pipStatusDot.className = 'status-dot alert';
  }

  const now     = new Date();
  const timeStr = now.toTimeString().split(' ')[0];
  addLogItem(timeStr, signalVal);

  if (visualAlertToggle.checked) {
    alertOverlay.classList.add('triggered');
    appContainer.classList.add('shake');

    if (pipAlertOverlay) {
      pipAlertOverlay.classList.add('triggered');
    }

    setTimeout(() => {
      alertOverlay.classList.remove('triggered');
      appContainer.classList.remove('shake');
      if (pipAlertOverlay) {
        pipAlertOverlay.classList.remove('triggered');
      }
    }, 280);
  }

  if (audioAlertToggle.checked && audioCtx) {
    try {
      const osc  = audioCtx.createOscillator();
      const gain = audioCtx.createGain();
      osc.type = 'sine';
      osc.frequency.setValueAtTime(880, audioCtx.currentTime);
      gain.gain.setValueAtTime(0, audioCtx.currentTime);
      gain.gain.linearRampToValueAtTime(0.18, audioCtx.currentTime + 0.01);
      gain.gain.exponentialRampToValueAtTime(0.001, audioCtx.currentTime + 0.14);
      osc.connect(gain);
      gain.connect(audioCtx.destination);
      osc.start();
      osc.stop(audioCtx.currentTime + 0.15);
    } catch (e) { /* ignore */ }
  }

  setTimeout(() => {
    if (isMonitoring) {
      statusText.textContent = '監視中';
      statusText.style.color = 'var(--clr-safe)';
      if (statusDot) statusDot.className = 'status-dot monitoring';

      // Restore PiP status
      if (pipStatusText) {
        pipStatusText.textContent = '監視中';
        pipStatusText.style.color = 'var(--clr-safe)';
      }
      if (pipStatusDot) {
        pipStatusDot.className = 'status-dot monitoring';
      }
    }
    warningCooldown = false;
  }, 500);
}

// ─── Log item with severity ───────────────────────────────────
function addLogItem(time, value) {
  const placeholder = document.getElementById('logPlaceholder');
  if (placeholder) placeholder.remove();

  const thresh = getThreshold();
  let severityClass, severityLabel, msgText;

  if (value >= thresh * 2.0) {
    severityClass = 'danger-high'; severityLabel = '強打'; msgText = '強打を検知';
  } else if (value >= thresh * 1.5) {
    severityClass = 'danger-mid';  severityLabel = '中打'; msgText = '中打を検知';
  } else {
    severityClass = 'danger-low';  severityLabel = '検知'; msgText = '打鍵を検知';
  }

  logData.unshift({ time, msg: msgText, severity: severityLabel, ratio: value.toFixed(2) });

  const item = document.createElement('div');
  item.className = `log-item ${severityClass}`;
  item.innerHTML = `
    <span class="log-time">${time}</span>
    <span class="log-msg">${msgText}</span>
    <span class="log-severity">${severityLabel}</span>
    <span class="log-value">${value.toFixed(2)}</span>`;
  logPanel.insertBefore(item, logPanel.firstChild);

  if (logPanel.children.length > 50) logPanel.removeChild(logPanel.lastChild);
  if (logData.length > 50) logData.pop();
}

// ─── Canvas rendering ─────────────────────────────────────────
function drawCanvas(timeData, signalRatio, threshold) {
  const W = visualizerCanvas.width;
  const H = visualizerCanvas.height;

  canvasCtx.clearRect(0, 0, W, H);

  // Background
  canvasCtx.fillStyle = '#0d1117';
  canvasCtx.fillRect(0, 0, W, H);

  // Grid
  canvasCtx.strokeStyle = 'rgba(255,255,255,0.03)';
  canvasCtx.lineWidth = 1;
  for (let x = 0; x < W; x += 50) {
    canvasCtx.beginPath();
    canvasCtx.moveTo(x, 0);
    canvasCtx.lineTo(x, H);
    canvasCtx.stroke();
  }
  canvasCtx.beginPath();
  canvasCtx.moveTo(0, H / 2);
  canvasCtx.lineTo(W, H / 2);
  canvasCtx.stroke();

  // Waveform — blue (#2980b9) safe / red (#e74c3c) alert
  const isAlert = signalRatio > threshold;
  canvasCtx.lineWidth = 2;
  canvasCtx.strokeStyle = isAlert
    ? 'rgba(231, 76,  60,  0.9)'   // #e74c3c
    : 'rgba( 41, 128, 185, 0.75)'; // #2980b9
  canvasCtx.beginPath();
  const sliceW = W / timeData.length;
  let x = 0;
  for (let i = 0; i < timeData.length; i++) {
    const v = timeData[i] / 128.0;
    const y = (v * H) / 2;
    i === 0 ? canvasCtx.moveTo(x, y) : canvasCtx.lineTo(x, y);
    x += sliceW;
  }
  canvasCtx.stroke();

  // Threshold dashed line
  const tY = H - Math.min(1.0, threshold / 5.0) * H;
  canvasCtx.strokeStyle = 'rgba(231, 76, 60, 0.5)';
  canvasCtx.lineWidth = 1;
  canvasCtx.setLineDash([4, 4]);
  canvasCtx.beginPath();
  canvasCtx.moveTo(0, tY);
  canvasCtx.lineTo(W, tY);
  canvasCtx.stroke();
  canvasCtx.setLineDash([]);
  canvasCtx.fillStyle = 'rgba(231, 76, 60, 0.6)';
  canvasCtx.font = '10px Inter, sans-serif';
  canvasCtx.fillText(`しきい値 ${threshold.toFixed(2)}`, 6, tY - 4);

  // [NEW v4] PiP Canvas Sync Drawing
  if (pipCanvas && pipCanvasCtx) {
    const W_pip = pipCanvas.width;
    const H_pip = pipCanvas.height;
    pipCanvasCtx.clearRect(0, 0, W_pip, H_pip);
    pipCanvasCtx.fillStyle = '#0d1117';
    pipCanvasCtx.fillRect(0, 0, W_pip, H_pip);

    pipCanvasCtx.strokeStyle = 'rgba(255,255,255,0.03)';
    pipCanvasCtx.lineWidth = 1;
    for (let px = 0; px < W_pip; px += 40) {
      pipCanvasCtx.beginPath();
      pipCanvasCtx.moveTo(px, 0);
      pipCanvasCtx.lineTo(px, H_pip);
      pipCanvasCtx.stroke();
    }
    pipCanvasCtx.beginPath();
    pipCanvasCtx.moveTo(0, H_pip / 2);
    pipCanvasCtx.lineTo(W_pip, H_pip / 2);
    pipCanvasCtx.stroke();

    pipCanvasCtx.lineWidth = 2;
    pipCanvasCtx.strokeStyle = isAlert ? 'rgba(231, 76, 60, 0.9)' : 'rgba(41, 128, 185, 0.75)';
    pipCanvasCtx.beginPath();
    const sliceW_pip = W_pip / timeData.length;
    let px = 0;
    for (let i = 0; i < timeData.length; i++) {
      const v = timeData[i] / 128.0;
      const y = (v * H_pip) / 2;
      i === 0 ? pipCanvasCtx.moveTo(px, y) : pipCanvasCtx.lineTo(px, y);
      px += sliceW_pip;
    }
    pipCanvasCtx.stroke();

    const tY_pip = H_pip - Math.min(1.0, threshold / 5.0) * H_pip;
    pipCanvasCtx.strokeStyle = 'rgba(231, 76, 60, 0.5)';
    pipCanvasCtx.lineWidth = 1;
    pipCanvasCtx.setLineDash([3, 3]);
    pipCanvasCtx.beginPath();
    pipCanvasCtx.moveTo(0, tY_pip);
    pipCanvasCtx.lineTo(W_pip, tY_pip);
    pipCanvasCtx.stroke();
    pipCanvasCtx.setLineDash([]);
  }
}

// ─── [NEW v4] Dark Mode Logic ───────────────────────────────
themeToggleBtn.addEventListener('click', () => {
  document.body.classList.toggle('dark-theme');
  const isDark = document.body.classList.contains('dark-theme');
  localStorage.setItem('keynoise-theme', isDark ? 'dark' : 'light');

  // 同時にPiPウインドウがあれば同期する
  if (pipWindow) {
    if (isDark) {
      pipWindow.document.body.classList.add('dark-theme');
    } else {
      pipWindow.document.body.classList.remove('dark-theme');
    }
  }
});

// 初期テーマ設定のロード
if (localStorage.getItem('keynoise-theme') === 'dark') {
  document.body.classList.add('dark-theme');
}

// ─── [NEW v4] Document Picture-in-Picture Logic ──────────────
pipBtn.addEventListener('click', async () => {
  if (pipWindow) {
    pipWindow.close();
    return;
  }
  await openPip();
});

async function openPip() {
  if (!('documentPictureInPicture' in window)) {
    alert('お使いのブラウザはDocument Picture-in-Picture APIに対応していません。ChromeやEdgeの最新版をお試しください。');
    return;
  }

  try {
    pipWindow = await window.documentPictureInPicture.requestWindow({
      width: 320,
      height: 380
    });

    // メインウインドウのCSSスタイルシートをPiPにコピーして適用
    [...document.styleSheets].forEach((styleSheet) => {
      try {
        const cssRules = [...styleSheet.cssRules].map((rule) => rule.cssText).join('');
        const style = pipWindow.document.createElement('style');
        style.textContent = cssRules;
        pipWindow.document.head.appendChild(style);
      } catch (e) {
        if (styleSheet.href) {
          const link = pipWindow.document.createElement('link');
          link.rel = 'stylesheet';
          link.href = styleSheet.href;
          pipWindow.document.head.appendChild(link);
        }
      }
    });

    // ダークモード状態を同期
    if (document.body.classList.contains('dark-theme')) {
      pipWindow.document.body.classList.add('dark-theme');
    }

    // PiPウインドウ内のDOMを設定
    pipWindow.document.body.innerHTML = `
      <div class="app-wrapper" style="padding: 12px; gap: 12px; min-height: 100vh; background: var(--bg); display: flex; flex-direction: column; justify-content: center;">
        <div id="pipAlertOverlay" class="alert-overlay"></div>
        <div class="card" style="padding: 16px; display: flex; flex-direction: column; gap: 16px;">
          
          <div style="display: flex; justify-content: space-between; align-items: center;">
            <div>
              <div class="status-label">状態</div>
              <div class="status-indicator" style="margin-top:2px;">
                <div id="pipStatusDot" class="status-dot"></div>
                <span id="pipStatusText" style="font-size: 1.2rem; font-weight:800;">${statusText.textContent}</span>
              </div>
            </div>
            <div style="text-align: right;">
              <div class="status-label">強打検知</div>
              <div style="font-size: 1.5rem; font-weight:800; color: var(--clr-base);"><span id="pipDetectionCount">${sessionDetectionCount}</span>回</div>
            </div>
          </div>

          <div style="display: flex; gap: 12px; align-items: stretch; height: 160px;">
            <div class="canvas-container" style="flex: 1; height: 100%;">
              <canvas id="pipVisualizerCanvas"></canvas>
            </div>
            
            <div class="gauge-block" style="min-width: 45px;">
              <div class="gauge-bar-wrapper" style="min-height: 120px; width: 28px;">
                <div id="pipGaugeBarFill" class="gauge-bar-fill" style="height: 0%;"></div>
              </div>
              <div id="pipGaugeVal" class="gauge-val" style="font-size:0.75rem;">0.0</div>
            </div>
          </div>
          
        </div>
      </div>
    `;

    // 描画同期用の参照を取得
    pipCanvas = pipWindow.document.getElementById('pipVisualizerCanvas');
    pipCanvasCtx = pipCanvas.getContext('2d');
    pipGaugeBarFill = pipWindow.document.getElementById('pipGaugeBarFill');
    pipGaugeVal = pipWindow.document.getElementById('pipGaugeVal');
    pipStatusText = pipWindow.document.getElementById('pipStatusText');
    pipStatusDot = pipWindow.document.getElementById('pipStatusDot');
    pipDetectionCount = pipWindow.document.getElementById('pipDetectionCount');
    pipAlertOverlay = pipWindow.document.getElementById('pipAlertOverlay');

    // Canvasサイズ初期化
    pipCanvas.width = pipCanvas.parentElement.clientWidth || 200;
    pipCanvas.height = 160;

    // 現在の監視状態に応じてスタイルクラスを付与
    if (isMonitoring) {
      pipStatusDot.className = 'status-dot monitoring';
      pipStatusText.style.color = 'var(--clr-safe)';
    } else {
      pipStatusDot.className = 'status-dot';
      pipStatusText.style.color = 'var(--txt-secondary)';
    }

    // 閉じるイベント時のクリーンアップ
    pipWindow.addEventListener('pagehide', () => {
      pipWindow = null;
      pipCanvas = null;
      pipCanvasCtx = null;
      pipGaugeBarFill = null;
      pipGaugeVal = null;
      pipStatusText = null;
      pipStatusDot = null;
      pipDetectionCount = null;
      pipAlertOverlay = null;
    });

  } catch (err) {
    console.error('PiPウィンドウの作成に失敗しました:', err);
  }
}

