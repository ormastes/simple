const { app, BrowserWindow } = require('electron');
const fs = require('fs');

app.commandLine.appendSwitch('enable-unsafe-webgpu');
app.commandLine.appendSwitch('ignore-gpu-blocklist');
app.commandLine.appendSwitch('force-color-profile', 'srgb');

const outPath = process.env.CWG_OUT || '/tmp/simple_chrome_webgpu_draw_evidence.json';
const width = Number(process.env.CWG_W || 96);
const height = Number(process.env.CWG_H || 64);
const rectX = Number(process.env.CWG_RECT_X || 8);
const rectY = Number(process.env.CWG_RECT_Y || 8);
const rectW = Number(process.env.CWG_RECT_W || 32);
const rectH = Number(process.env.CWG_RECT_H || 24);
const color = process.env.CWG_COLOR || '#33aa66';
const mode = process.env.CWG_MODE || 'rect';
const sourceOrigin = process.env.CWG_SOURCE_ORIGIN || '';
const payloadByteCount = Number(process.env.CWG_PAYLOAD_BYTE_COUNT || 0);
const payloadChecksum = Number(process.env.CWG_PAYLOAD_CHECKSUM || 0);
const triangleCount = Number(process.env.CWG_TRIANGLE_COUNT || 0);
const tri = {
  x1: Number(process.env.CWG_TRI_X1 || 0),
  y1: Number(process.env.CWG_TRI_Y1 || 1),
  z1: Number(process.env.CWG_TRI_Z1 || 0),
  x2: Number(process.env.CWG_TRI_X2 || -1),
  y2: Number(process.env.CWG_TRI_Y2 || -1),
  z2: Number(process.env.CWG_TRI_Z2 || 0),
  x3: Number(process.env.CWG_TRI_X3 || 1),
  y3: Number(process.env.CWG_TRI_Y3 || -1),
  z3: Number(process.env.CWG_TRI_Z3 || 0),
};

function evidence(status, patch = {}) {
  return {
    status,
    diagnostic_text: String(patch.diagnostic_text || '').replace(/[\\"]/g, "'"),
    pixel_checksum: patch.pixel_checksum || 0,
    non_background_pixels: patch.non_background_pixels || 0,
    capture_width: patch.capture_width || 0,
    capture_height: patch.capture_height || 0,
    adapter: Boolean(patch.adapter),
    adapter_info: String(patch.adapter_info || '').replace(/[\\"]/g, "'"),
    fallback_adapter: Boolean(patch.fallback_adapter),
    device_configured: Boolean(patch.device_configured),
    pipeline_valid: Boolean(patch.pipeline_valid),
    render_pass_count: patch.render_pass_count || 0,
    draw_call_count: patch.draw_call_count || 0,
    presented: Boolean(patch.presented),
    source_origin: String(patch.source_origin || sourceOrigin).replace(/[\\"]/g, "'"),
    payload_byte_count: patch.payload_byte_count || payloadByteCount,
    payload_checksum: patch.payload_checksum || payloadChecksum,
    triangle_count: patch.triangle_count || triangleCount,
  };
}

function writeEvidence(data) {
  fs.writeFileSync(outPath, JSON.stringify(data));
}

function html() {
  const payload = { width, height, rectX, rectY, rectW, rectH, color, mode, sourceOrigin, payloadByteCount, payloadChecksum, triangleCount, tri };
  return `<!doctype html><html><body style="margin:0;background:#000">
<canvas id="c" width="${width}" height="${height}" style="width:${width}px;height:${height}px"></canvas>
<script>
const payload = JSON.parse(${JSON.stringify(JSON.stringify(payload))});
function fail(status, diagnostic_text) {
  window.__simpleWebGPUEvidence = { status, diagnostic_text, pixel_checksum:0, non_background_pixels:0, capture_width:0, capture_height:0, adapter:false, adapter_info:'', fallback_adapter:false, device_configured:false, pipeline_valid:false, render_pass_count:0, draw_call_count:0, presented:false, source_origin:payload.sourceOrigin, payload_byte_count:payload.payloadByteCount, payload_checksum:payload.payloadChecksum, triangle_count:payload.triangleCount };
}
function colorToVec(hex) {
  const n = Number.parseInt(hex.replace('#', ''), 16);
  return [((n >> 16) & 255) / 255, ((n >> 8) & 255) / 255, (n & 255) / 255, 1];
}
function vertexData() {
  if (payload.mode === 'simple3d-triangle') {
    return { verts: new Float32Array([payload.tri.x1,payload.tri.y1,payload.tri.z1, payload.tri.x2,payload.tri.y2,payload.tri.z2, payload.tri.x3,payload.tri.y3,payload.tri.z3]), stride: 12, format: 'float32x3', count: 3, vertex: '@vertex fn vs(@location(0) pos: vec3f) -> @builtin(position) vec4f { return vec4f(pos, 1.0); }' };
  }
  const x0 = payload.rectX / payload.width * 2 - 1;
  const y0 = 1 - payload.rectY / payload.height * 2;
  const x1 = (payload.rectX + payload.rectW) / payload.width * 2 - 1;
  const y1 = 1 - (payload.rectY + payload.rectH) / payload.height * 2;
  return { verts: new Float32Array([x0,y0, x1,y0, x0,y1, x0,y1, x1,y0, x1,y1]), stride: 8, format: 'float32x2', count: 6, vertex: '@vertex fn vs(@location(0) pos: vec2f) -> @builtin(position) vec4f { return vec4f(pos, 0.0, 1.0); }' };
}
(async () => {
  try {
    if (!navigator.gpu) return fail('host-unavailable:navigator-gpu', 'navigator.gpu missing');
    const adapter = await navigator.gpu.requestAdapter();
    if (!adapter) return fail('host-unavailable:adapter', 'requestAdapter returned null');
    if (adapter.isFallbackAdapter) return fail('host-unavailable:fallback-adapter', 'Chrome reported fallback WebGPU adapter');
    const adapterInfo = adapter.info ? JSON.stringify(adapter.info) : '';
    const device = await adapter.requestDevice();
    const canvas = document.getElementById('c');
    const context = canvas.getContext('webgpu');
    if (!context) return fail('host-unavailable:canvas-webgpu', 'canvas webgpu context missing');
    const format = navigator.gpu.getPreferredCanvasFormat();
    context.configure({ device, format, alphaMode: 'premultiplied' });
    const rgba = colorToVec(payload.color);
    const vertex = vertexData();
    const shader = device.createShaderModule({ code: vertex.vertex + ' @fragment fn fs() -> @location(0) vec4f { return vec4f(' + rgba.join(',') + '); }' });
    const pipeline = device.createRenderPipeline({
      layout: 'auto',
      vertex: { module: shader, entryPoint: 'vs', buffers: [{ arrayStride: vertex.stride, attributes: [{ shaderLocation: 0, offset: 0, format: vertex.format }] }] },
      fragment: { module: shader, entryPoint: 'fs', targets: [{ format }] },
      primitive: { topology: 'triangle-list' },
    });
    const verts = vertex.verts;
    const vb = device.createBuffer({ size: verts.byteLength, usage: GPUBufferUsage.VERTEX | GPUBufferUsage.COPY_DST });
    device.queue.writeBuffer(vb, 0, verts);
    const encoder = device.createCommandEncoder();
    const pass = encoder.beginRenderPass({ colorAttachments: [{ view: context.getCurrentTexture().createView(), clearValue: { r:0, g:0, b:0, a:1 }, loadOp: 'clear', storeOp: 'store' }] });
    pass.setPipeline(pipeline);
    pass.setVertexBuffer(0, vb);
    pass.draw(vertex.count);
    pass.end();
    device.queue.submit([encoder.finish()]);
    await device.queue.onSubmittedWorkDone();
    window.__simpleWebGPUEvidence = { status:'ok', diagnostic_text:'', pixel_checksum:0, non_background_pixels:0, capture_width:0, capture_height:0, adapter:true, adapter_info:adapterInfo, fallback_adapter:false, device_configured:true, pipeline_valid:true, render_pass_count:1, draw_call_count:1, presented:true, source_origin:payload.sourceOrigin, payload_byte_count:payload.payloadByteCount, payload_checksum:payload.payloadChecksum, triangle_count:payload.triangleCount };
  } catch (err) {
    fail('host-unavailable:electron-launch', String(err && err.message || err));
  }
})();
</script></body></html>`;
}

async function waitForEvidence(webContents) {
  const started = Date.now();
  while (Date.now() - started < 5000) {
    const value = await webContents.executeJavaScript('window.__simpleWebGPUEvidence || null');
    if (value) return value;
    await new Promise(resolve => setTimeout(resolve, 50));
  }
  throw new Error('timed out waiting for window.__simpleWebGPUEvidence');
}

app.whenReady().then(async () => {
  const win = new BrowserWindow({
    width,
    height,
    show: false,
    webPreferences: { offscreen: true, sandbox: false },
    backgroundColor: '#000000',
  });
  win.webContents.setFrameRate(30);
  try {
    await win.loadURL('data:text/html;charset=utf-8,' + encodeURIComponent(html()));
    const pageEvidence = await waitForEvidence(win.webContents);
    if (pageEvidence.status === 'ok') {
      const img = await win.webContents.capturePage();
      const bmp = img.toBitmap();
      const size = img.getSize();
      let checksum = 0;
      let nonBackground = 0;
      for (let i = 0; i < bmp.length; i += 4) {
        const b = bmp[i], g = bmp[i + 1], r = bmp[i + 2], a = bmp[i + 3];
        checksum = (checksum + r * 3 + g * 5 + b * 7 + a) >>> 0;
        if (r !== 0 || g !== 0 || b !== 0) nonBackground += 1;
      }
      if (size.width <= 0 || size.height <= 0 || checksum <= 0 || nonBackground <= 0) {
        writeEvidence(evidence('host-unavailable:empty-capture', { ...pageEvidence, diagnostic_text: 'Chrome WebGPU submitted but captured no non-background pixels' }));
        win.destroy();
        app.exit(0);
        return;
      }
      writeEvidence(evidence('ok', { ...pageEvidence, pixel_checksum: checksum, non_background_pixels: nonBackground, capture_width: size.width, capture_height: size.height }));
    } else {
      writeEvidence(evidence(pageEvidence.status, pageEvidence));
    }
    win.destroy();
    app.exit(0);
  } catch (err) {
    writeEvidence(evidence('host-unavailable:timeout', { diagnostic_text: String(err && err.message || err) }));
    win.destroy();
    app.exit(0);
  }
});
