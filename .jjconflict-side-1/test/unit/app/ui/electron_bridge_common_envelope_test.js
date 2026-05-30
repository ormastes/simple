const assert = require('assert');
const {
  commonInputEnvelope,
  renderEnvelopeMetadata,
  renderEnvelopeScript,
} = require('../../../../src/app/ui.electron/bridge_envelopes.js');
const { parseCliArgs } = require('../../../../src/app/ui.electron/bridge.js');

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

console.log('electron bridge common envelope contract ok');
