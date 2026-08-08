const { app, BrowserWindow } = require('electron');
const fs = require('fs');

app.commandLine.appendSwitch('enable-unsafe-webgpu');
app.commandLine.appendSwitch('ignore-gpu-blocklist');
app.commandLine.appendSwitch('force-color-profile', 'srgb');

const outPath = process.env.CWC_OUT || '/tmp/simple_chrome_webgpu_compute_evidence.json';
const count = Number(process.env.CWC_COUNT || 8);
const operation = process.env.CWC_OPERATION || 'u32_add';
const fillValue = Number(process.env.CWC_FILL_VALUE || 287454020) >>> 0;
const payloadByteCount = Number(process.env.CWC_PAYLOAD_BYTE_COUNT || 0);
const payloadChecksum = Number(process.env.CWC_PAYLOAD_CHECKSUM || 0);
const defaultWgslSource = '@group(0) @binding(0) var<storage, read> a: array<u32>; @group(0) @binding(1) var<storage, read> b: array<u32>; @group(0) @binding(2) var<storage, read_write> out: array<u32>; @compute @workgroup_size(64) fn simple_webgpu_add_u32(@builtin(global_invocation_id) global_id: vec3<u32>) { let i = global_id.x; if (i < arrayLength(&out)) { out[i] = a[i] + b[i]; } }';
const wgslSource = process.env.CWC_WGSL_SOURCE || defaultWgslSource;
const entryName = process.env.CWC_ENTRY_NAME || 'simple_webgpu_add_u32';
const sourceOrigin = process.env.CWC_SOURCE_ORIGIN || (process.env.CWC_WGSL_SOURCE ? 'external' : 'helper-default');

function textChecksum(value) {
  let out = 0;
  for (let i = 0; i < value.length; i += 1) out = (out + value.charCodeAt(i)) >>> 0;
  return out;
}

function clean(value) {
  return String(value || '').replace(/[\\"]/g, "'");
}

function evidence(status, patch = {}) {
  const outputCount = Number(patch.output_count || 0);
  const outputMatches = Boolean(patch.output_matches);
  const mismatchCount = Number.isFinite(patch.mismatch_count)
    ? patch.mismatch_count
    : (outputMatches ? 0 : outputCount);
  const readbackByteCount = Number.isFinite(patch.readback_byte_count)
    ? patch.readback_byte_count
    : outputCount * 4;
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
    backend_target: clean(patch.backend_target || 'webgpu'),
    source_format: clean(patch.source_format || 'wgsl'),
    binary_format: clean(patch.binary_format || 'source'),
    tool_hint: clean(patch.tool_hint || 'browser-webgpu-host-import'),
    entry_name: clean(patch.entry_name || entryName),
    operation: clean(patch.operation || operation),
    source_origin: clean(patch.source_origin || sourceOrigin),
    source_byte_count: patch.source_byte_count || wgslSource.length,
    source_checksum: patch.source_checksum || textChecksum(wgslSource),
    payload_byte_count: patch.payload_byte_count || payloadByteCount,
    payload_checksum: patch.payload_checksum || payloadChecksum,
    element_count: patch.element_count || count,
    dispatch_count: patch.dispatch_count || 0,
    workgroup_count: patch.workgroup_count || 0,
    submitted: Boolean(patch.submitted),
    readback_valid: Boolean(patch.readback_valid),
    output_count: outputCount,
    output_checksum: patch.output_checksum || 0,
    expected_checksum: patch.expected_checksum || 0,
    output_matches: outputMatches,
    mismatch_count: mismatchCount,
    readback_byte_count: readbackByteCount,
  };
}

function writeEvidence(data) {
  fs.writeFileSync(outPath, JSON.stringify(data));
}

function html() {
  return `<!doctype html><html><body>
<script>
const count = ${JSON.stringify(count)};
const operation = ${JSON.stringify(operation)};
const fillValue = ${JSON.stringify(fillValue)};
const payloadByteCount = ${JSON.stringify(payloadByteCount)};
const payloadChecksum = ${JSON.stringify(payloadChecksum)};
const runtimeState = { adapter:false, adapter_info:'', fallback_adapter:false, device_configured:false, shader_valid:false, pipeline_valid:false, bind_group_valid:false };
function mark(patch) {
  Object.assign(runtimeState, patch);
}
function fail(status, diagnostic_text, patch = {}) {
  const state = Object.assign({}, runtimeState, patch);
  window.__simpleWebGPUComputeEvidence = { status, diagnostic_text, backend_target:'webgpu', source_format:'wgsl', binary_format:'source', tool_hint:'browser-webgpu-host-import', entry_name:${JSON.stringify(entryName)}, operation, source_origin:${JSON.stringify(sourceOrigin)}, source_byte_count:${JSON.stringify(wgslSource.length)}, source_checksum:${JSON.stringify(textChecksum(wgslSource))}, payload_byte_count:payloadByteCount, payload_checksum:payloadChecksum, element_count:count, adapter:Boolean(state.adapter), adapter_info:state.adapter_info || '', fallback_adapter:Boolean(state.fallback_adapter), device_configured:Boolean(state.device_configured), shader_valid:Boolean(state.shader_valid), pipeline_valid:Boolean(state.pipeline_valid), bind_group_valid:Boolean(state.bind_group_valid), dispatch_count:0, workgroup_count:0, submitted:false, readback_valid:false, output_count:0, output_checksum:0, expected_checksum:0, output_matches:false, mismatch_count:0, readback_byte_count:0 };
}
function checksum(values) {
  let out = 0;
  for (const value of values) out = (out + Number(value)) >>> 0;
  return out;
}
function countMismatches(values, expected) {
  if (values.length !== expected.length) return Math.max(values.length, expected.length);
  let mismatches = 0;
  for (let i = 0; i < values.length; i += 1) {
    if (values[i] !== expected[i]) mismatches += 1;
  }
  return mismatches;
}
(async () => {
  try {
    if (!navigator.gpu) return fail('host-unavailable:navigator-gpu', 'navigator.gpu missing');
    const adapter = await navigator.gpu.requestAdapter();
    if (!adapter) return fail('host-unavailable:adapter', 'requestAdapter returned null');
    const adapterInfo = adapter.info ? JSON.stringify(adapter.info) : '';
    mark({ adapter:true, adapter_info:adapterInfo, fallback_adapter:Boolean(adapter.isFallbackAdapter) });
    if (adapter.isFallbackAdapter) return fail('host-unavailable:fallback-adapter', 'Chrome reported fallback WebGPU adapter');
    const device = await adapter.requestDevice();
    mark({ device_configured:true });
    const shader = device.createShaderModule({ code: ${JSON.stringify(wgslSource)} });
    const compilationInfo = shader.getCompilationInfo ? await shader.getCompilationInfo() : { messages: [] };
    const shaderErrors = (compilationInfo.messages || []).filter(message => message.type === 'error');
    if (shaderErrors.length > 0) return fail('compile-failed:wgsl', shaderErrors.map(message => message.message).join('; '));
    mark({ shader_valid:true });
    const pipeline = device.createComputePipeline({ layout: 'auto', compute: { module: shader, entryPoint: ${JSON.stringify(entryName)} } });
    mark({ pipeline_valid:true });
    if (operation === 'simple2d_fill') {
      const byteLength = count * 4;
      const dst = device.createBuffer({ size: byteLength, usage: GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_SRC });
      const paramsBytes = new ArrayBuffer(64);
      const paramsView = new DataView(paramsBytes);
      paramsView.setUint32(0, fillValue, true);
      paramsView.setUint32(4, count, true);
      paramsView.setUint32(12, count, true);
      paramsView.setUint32(16, 1, true);
      const params = device.createBuffer({ size: 64, usage: GPUBufferUsage.UNIFORM | GPUBufferUsage.COPY_DST });
      const readback = device.createBuffer({ size: byteLength, usage: GPUBufferUsage.COPY_DST | GPUBufferUsage.MAP_READ });
      device.queue.writeBuffer(params, 0, paramsBytes);
      const bindGroup = device.createBindGroup({ layout: pipeline.getBindGroupLayout(0), entries: [
        { binding: 1, resource: { buffer: dst } },
        { binding: 3, resource: { buffer: params } },
      ] });
      mark({ bind_group_valid:true });
      const encoder = device.createCommandEncoder();
      const pass = encoder.beginComputePass();
      pass.setPipeline(pipeline);
      pass.setBindGroup(0, bindGroup);
      const workgroups = Math.ceil(count / 64);
      pass.dispatchWorkgroups(workgroups);
      pass.end();
      encoder.copyBufferToBuffer(dst, 0, readback, 0, byteLength);
      device.queue.submit([encoder.finish()]);
      await device.queue.onSubmittedWorkDone();
      await readback.mapAsync(GPUMapMode.READ);
      const values = new Uint32Array(readback.getMappedRange().slice(0));
      readback.unmap();
      const expected = new Uint32Array(count);
      expected.fill(fillValue);
      const outputChecksum = checksum(values);
      const expectedChecksum = checksum(expected);
      const mismatches = countMismatches(values, expected);
      window.__simpleWebGPUComputeEvidence = { status: mismatches === 0 ? 'ok' : 'processing-mismatch:readback', diagnostic_text: mismatches === 0 ? '' : 'Chrome WebGPU Simple2D fill readback did not match expected data', backend_target:'webgpu', source_format:'wgsl', binary_format:'source', tool_hint:'browser-webgpu-host-import', entry_name:${JSON.stringify(entryName)}, operation, source_origin:${JSON.stringify(sourceOrigin)}, source_byte_count:${JSON.stringify(wgslSource.length)}, source_checksum:${JSON.stringify(textChecksum(wgslSource))}, payload_byte_count:payloadByteCount, payload_checksum:payloadChecksum, element_count:count, adapter:true, adapter_info:adapterInfo, fallback_adapter:false, device_configured:true, shader_valid:true, pipeline_valid:true, bind_group_valid:true, dispatch_count:1, workgroup_count:workgroups, submitted:true, readback_valid:values.length === count, output_count:values.length, output_checksum:outputChecksum, expected_checksum:expectedChecksum, output_matches:mismatches === 0, mismatch_count:mismatches, readback_byte_count:values.length * 4 };
      return;
    }
    if (operation !== 'u32_add') return fail('invalid:operation', 'unsupported Chrome WebGPU compute operation: ' + operation);
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
    mark({ bind_group_valid:true });
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
    const mismatches = countMismatches(values, expected);
    window.__simpleWebGPUComputeEvidence = { status:'ok', diagnostic_text:'', backend_target:'webgpu', source_format:'wgsl', binary_format:'source', tool_hint:'browser-webgpu-host-import', entry_name:${JSON.stringify(entryName)}, operation:'u32_add', source_origin:${JSON.stringify(sourceOrigin)}, source_byte_count:${JSON.stringify(wgslSource.length)}, source_checksum:${JSON.stringify(textChecksum(wgslSource))}, payload_byte_count:payloadByteCount, payload_checksum:payloadChecksum, element_count:count, adapter:true, adapter_info:adapterInfo, fallback_adapter:false, device_configured:true, shader_valid:true, pipeline_valid:true, bind_group_valid:true, dispatch_count:1, workgroup_count:workgroups, submitted:true, readback_valid:values.length === count, output_count:values.length, output_checksum:outputChecksum, expected_checksum:expectedChecksum, output_matches:mismatches === 0, mismatch_count:mismatches, readback_byte_count:values.length * 4 };
  } catch (err) {
    const status = runtimeState.adapter || runtimeState.device_configured ? 'processing-failed:compute-launch' : 'host-unavailable:compute-launch';
    fail(status, String(err && err.message || err));
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
    if (pageEvidence.status === 'ok' && (!pageEvidence.output_matches || pageEvidence.output_count !== count)) {
      writeEvidence(evidence('processing-mismatch:readback', { ...pageEvidence, diagnostic_text: 'Chrome WebGPU compute completed but readback did not match expected data' }));
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
