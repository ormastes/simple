const assert = require('assert');
const {
  commonInputEnvelope,
  renderEnvelopeMetadata,
  renderEnvelopeScript,
} = require('../../../../src/app/ui.electron/bridge_envelopes.js');
const { electronWmInitScript, parseCliArgs, simpleProcessArgs: bridgeSimpleProcessArgs } = require('../../../../src/app/ui.electron/bridge.js');
const { electronLiveSmokeProofScript } = require('../../../../src/app/ui.electron/bridge.js');

const renderLine = JSON.stringify({
  type: 'render',
  target: 'electron',
  surface_id: 'main',
  width: 1280,
  height: 720,
  html: '<main>Electron</main>',
});

const envelope = renderEnvelopeMetadata(JSON.parse(renderLine));
assert.deepStrictEqual(envelope, {
  target: 'electron',
  surface_id: 'main',
  width: 1280,
  height: 720,
});

const script = renderEnvelopeScript(JSON.parse(renderLine));
assert(script.includes('__SIMPLE_WEB_RENDER_ENVELOPE__'));
assert(script.includes('"target":"electron"'));
assert(script.includes('"surface_id":"main"'));
assert(script.includes('"body_html_length":21'));
assert(script.includes('"css_length":0'));
assert(script.includes('<main>Electron</main>'));

const resize = commonInputEnvelope('resize', { x: 640, y: 480 });
assert.deepStrictEqual(resize, {
  type: 'input',
  target: 'electron',
  surface_id: 'main',
  event_type: 'resize',
  target_id: '',
  key: '',
  value: '',
  x: 640,
  y: 480,
  dx: 0,
  dy: 0,
  button: '',
});

const key = commonInputEnvelope('key', { key: 'Enter' });
assert.strictEqual(key.type, 'input');
assert.strictEqual(key.target, 'electron');
assert.strictEqual(key.event_type, 'key');
assert.strictEqual(key.key, 'Enter');

const parsed = parseCliArgs(['--simple-bin', 'bin/simple', '--entry', 'examples/ui/hello_tauri.ui.sdn']);
assert.strictEqual(parsed.simpleBin, 'bin/simple');
assert.strictEqual(parsed.entry, 'examples/ui/hello_tauri.ui.sdn');
assert.strictEqual(parsed.port, 3000);

const splArgs = bridgeSimpleProcessArgs('examples/ui/electron_wm.spl');
assert.strictEqual(splArgs[0], 'run');
assert(splArgs[1].endsWith('examples/ui/electron_wm.spl'));

const sdnArgs = bridgeSimpleProcessArgs('examples/ui/hello_tauri.ui.sdn');
assert.strictEqual(sdnArgs[0], 'run');
assert(sdnArgs[1].endsWith('src/app/ui.electron/app.spl'));
assert(sdnArgs[2].endsWith('examples/ui/hello_tauri.ui.sdn'));

const wmInit = electronWmInitScript();
assert(wmInit.includes('pointerdown'));
assert(wmInit.includes('pointermove'));
assert(wmInit.includes('bindDrag'));
assert(wmInit.includes('notifyMove'));
assert(wmInit.includes('wm_move:'));
assert(wmInit.includes('cursor:grab'));
assert(wmInit.includes('bindWindowEvents'));
assert(wmInit.includes('sendWindowAction'));
assert(wmInit.includes('sendWindowKey'));
assert(wmInit.includes('sendWindowInput'));
assert(wmInit.includes('sendWindowMouse'));
assert(wmInit.includes('body.tabIndex = 0'));
assert(wmInit.includes('event_type: eventType'));
assert(wmInit.includes("type: 'input'"));
assert(wmInit.includes("sendWindowMouse(id, 'mouse_down'"));
assert(wmInit.includes("target_id: targetId"));

const liveSmokeProof = electronLiveSmokeProofScript();
assert(liveSmokeProof.includes('performance_now_available'));
assert(liveSmokeProof.includes('animation_frame_count'));
assert(liveSmokeProof.includes('css_animation_probe'));
assert(liveSmokeProof.includes('blur_or_tolerance_used'));
assert(liveSmokeProof.includes('body_text_sample'));

const bridgeSource = require('fs').readFileSync(require('path').join(__dirname, '../../../../src/app/ui.electron/bridge.js'), 'utf8');
assert(bridgeSource.includes("SIMPLE_UI_BACKEND: 'electron'"));
assert(bridgeSource.includes("SIMPLE_EXECUTION_MODE"));
assert(bridgeSource.includes("SIMPLE_TIMEOUT_SECONDS"));
assert(bridgeSource.includes('mdiProofInputFrames.push(envelope)'));
assert(bridgeSource.includes('bridgeIpcFrameCount'));
assert(bridgeSource.includes('bridgeBodyActionFrameRouted'));
assert(bridgeSource.includes('bridgeMinimizeFrameRouted'));
assert(bridgeSource.includes('bridgeMaximizeFrameRouted'));
assert(bridgeSource.includes('bridgeCloseFrameRouted'));
assert(bridgeSource.includes('trafficMinimizeRouted'));
assert(bridgeSource.includes('trafficMaximizeRouted'));
assert(bridgeSource.includes('trafficCloseRouted'));

console.log('electron bridge common envelope contract ok');
