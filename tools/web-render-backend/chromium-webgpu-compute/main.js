const { app, BrowserWindow } = require('electron');
const fs = require('fs');

app.commandLine.appendSwitch('enable-unsafe-webgpu');
app.commandLine.appendSwitch('ignore-gpu-blocklist');
app.commandLine.appendSwitch('force-color-profile', 'srgb');

const outPath = process.env.CWC_OUT || '/tmp/simple_chrome_webgpu_compute_evidence.json';
const count = Number(process.env.CWC_COUNT || 8);

function clean(value) {
  return String(value || '').replace(/[\\"]/g, "'");
}

function evidence(status, patch = {}) {
  return {
    status,
    diagnostic_text: clean(patch.diagnostic_text),
    adapter: Boolean(patch.adapter),
    adapter_info: clean(patch.adapter_info),
    fallback_adapter: Boolean(patch.fallback_adapter),
    device_configured: Boolean(patch.device_configured),
    shader_valid: Boolean(patch.shader_valid),
    pipeline_valid: Boolean(patch.pipeline_valid),
    bind_group_valid: Boolean(patch.bind_group_valid),
    dispatch_count: patch.dispatch_count || 0,
    workgroup_count: patch.workgroup_count || 0,
    submitted: Boolean(patch.submitted),
    readback_valid: Boolean(patch.readback_valid),
    output_count: patch.output_count || 0,
    output_checksum: patch.output_checksum || 0,
    expected_checksum: patch.expected_checksum || 0,
    output_matches: Boolean(patch.output_matches),
  };
}

function writeEvidence(data) {
  fs.writeFileSync(outPath, JSON.stringify(data));
}

function html() {
  return `<!doctype html><html><body>
<script>
const count = ${JSON.stringify(count)};
function fail(status, diagnostic_text) {
  window.__simpleWebGPUComputeEvidence = { status, diagnostic_text, adapter:false, adapter_info:'', fallback_adapter:false, device_configured:false, shader_valid:false, pipeline_valid:false, bind_group_valid:false, dispatch_count:0, workgroup_count:0, submitted:false, readback_valid:false, output_count:0, output_checksum:0, expected_checksum:0, output_matches:false };
}
function checksum(values) {
  let out = 0;
  for (const value of values) out = (out + Number(value)) >>> 0;
  return out;
}
(async () => {
  try {
    if (!navigator.gpu) return fail('host-unavailable:navigator-gpu', 'navigator.gpu missing');
    const adapter = await navigator.gpu.requestAdapter();
    if (!adapter) return fail('host-unavailable:adapter', 'requestAdapter returned null');
    if (adapter.isFallbackAdapter) return fail('host-unavailable:fallback-adapter', 'Chrome reported fallback WebGPU adapter');
    const adapterInfo = adapter.info ? JSON.stringify(adapter.info) : '';
    const device = await adapter.requestDevice();
    const shader = device.createShaderModule({ code: '@group(0) @binding(0) var<storage, read> a: array<u32>; @group(0) @binding(1) var<storage, read> b: array<u32>; @group(0) @binding(2) var<storage, read_write> out: array<u32>; @compute @workgroup_size(64) fn main(@builtin(global_invocation_id) id: vec3<u32>) { let i = id.x; if (i < arrayLength(&out)) { out[i] = a[i] + b[i]; } }' });
    const pipeline = device.createComputePipeline({ layout: 'auto', compute: { module: shader, entryPoint: 'main' } });
    const byteLength = count * 4;
    const aValues = new Uint32Array(count);
    const bValues = new Uint32Array(count);
    const expected = new Uint32Array(count);
    for (let i = 0; i < count; i += 1) {
      aValues[i] = i + 1;
      bValues[i] = (i + 1) * 10;
      expected[i] = aValues[i] + bValues[i];
    }
    const a = device.createBuffer({ size: byteLength, usage: GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_DST });
    const b = device.createBuffer({ size: byteLength, usage: GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_DST });
    const out = device.createBuffer({ size: byteLength, usage: GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_SRC });
    const readback = device.createBuffer({ size: byteLength, usage: GPUBufferUsage.COPY_DST | GPUBufferUsage.MAP_READ });
    device.queue.writeBuffer(a, 0, aValues);
    device.queue.writeBuffer(b, 0, bValues);
    const bindGroup = device.createBindGroup({ layout: pipeline.getBindGroupLayout(0), entries: [
      { binding: 0, resource: { buffer: a } },
      { binding: 1, resource: { buffer: b } },
      { binding: 2, resource: { buffer: out } },
    ] });
    const encoder = device.createCommandEncoder();
    const pass = encoder.beginComputePass();
    pass.setPipeline(pipeline);
    pass.setBindGroup(0, bindGroup);
    const workgroups = Math.ceil(count / 64);
    pass.dispatchWorkgroups(workgroups);
    pass.end();
    encoder.copyBufferToBuffer(out, 0, readback, 0, byteLength);
    device.queue.submit([encoder.finish()]);
    await device.queue.onSubmittedWorkDone();
    await readback.mapAsync(GPUMapMode.READ);
    const values = new Uint32Array(readback.getMappedRange().slice(0));
    readback.unmap();
    const outputChecksum = checksum(values);
    const expectedChecksum = checksum(expected);
    let matches = values.length === expected.length;
    for (let i = 0; i < values.length && matches; i += 1) {
      if (values[i] !== expected[i]) matches = false;
    }
    window.__simpleWebGPUComputeEvidence = { status:'ok', diagnostic_text:'', adapter:true, adapter_info:adapterInfo, fallback_adapter:false, device_configured:true, shader_valid:true, pipeline_valid:true, bind_group_valid:true, dispatch_count:1, workgroup_count:workgroups, submitted:true, readback_valid:values.length === count, output_count:values.length, output_checksum:outputChecksum, expected_checksum:expectedChecksum, output_matches:matches };
  } catch (err) {
    fail('host-unavailable:compute-launch', String(err && err.message || err));
  }
})();
</script></body></html>`;
}

async function waitForEvidence(webContents) {
  const started = Date.now();
  while (Date.now() - started < 5000) {
    const value = await webContents.executeJavaScript('window.__simpleWebGPUComputeEvidence || null');
    if (value) return value;
    await new Promise(resolve => setTimeout(resolve, 50));
  }
  throw new Error('timed out waiting for window.__simpleWebGPUComputeEvidence');
}

app.whenReady().then(async () => {
  const win = new BrowserWindow({
    width: 120,
    height: 80,
    show: false,
    webPreferences: { offscreen: true, sandbox: false },
  });
  try {
    await win.loadURL('data:text/html;charset=utf-8,' + encodeURIComponent(html()));
    const pageEvidence = await waitForEvidence(win.webContents);
    if (pageEvidence.status === 'ok' && (!pageEvidence.output_matches || pageEvidence.output_checksum <= 0 || pageEvidence.expected_checksum <= 0 || pageEvidence.output_count !== count)) {
      writeEvidence(evidence('host-unavailable:compute-mismatch', { ...pageEvidence, diagnostic_text: 'Chrome WebGPU compute completed but readback did not match expected data' }));
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
