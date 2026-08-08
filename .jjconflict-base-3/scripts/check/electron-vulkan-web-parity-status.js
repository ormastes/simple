#!/usr/bin/env node
const fs = require("fs");

const electronPath = process.argv[2] || "";
const vulkanPath = process.argv[3] || "";
const electronProofPath = process.argv[4] || "";
const expectedWidthProvided = process.argv.length > 5 && process.argv[5] !== "";
const expectedHeightProvided = process.argv.length > 6 && process.argv[6] !== "";
const expectedWidth = Number(process.argv[5] || 0);
const expectedHeight = Number(process.argv[6] || 0);
const expectedArgbProvided = process.argv.length > 7 && process.argv[7] !== "";
const expectedArgb = expectedArgbProvided ? Number(process.argv[7]) : 0;
const expectedRemoteDebuggingPortProvided = process.argv.length > 8 && process.argv[8] !== "";
const expectedRemoteDebuggingPort = String(process.argv[8] || "");
const expectedCapturedArgbPathProvided = process.argv.length > 9 && process.argv[9] !== "";
const expectedCapturedArgbPath = String(process.argv[9] || "");
const expectedHtmlPathProvided = process.argv.length > 10 && process.argv[10] !== "";
const expectedHtmlPath = String(process.argv[10] || "");
const expectedHtmlSha256Provided = process.argv.length > 11 && process.argv[11] !== "";
const expectedHtmlSha256 = String(process.argv[11] || "");
const expectedPngPathProvided = process.argv.length > 12 && process.argv[12] !== "";
const expectedPngPath = String(process.argv[12] || "");
const expectedPngSha256Provided = process.argv.length > 13 && process.argv[13] !== "";
const expectedPngSha256 = String(process.argv[13] || "");
const expectedCapturedArgbSha256Provided = process.argv.length > 14 && process.argv[14] !== "";
const expectedCapturedArgbSha256 = String(process.argv[14] || "");
const expectedVulkanRunIdProvided = process.argv.length > 15 && process.argv[15] !== "";
const expectedVulkanRunId = String(process.argv[15] || "");
const expectedVulkanJsonPathProvided = process.argv.length > 16 && process.argv[16] !== "";
const expectedVulkanJsonPath = String(process.argv[16] || "");
const expectedVulkanJsonSha256Provided = process.argv.length > 17 && process.argv[17] !== "";
const expectedVulkanJsonSha256 = String(process.argv[17] || "");

function emit(key, value) {
  console.log(`${key}=${value === undefined || value === null ? "" : value}`);
}

function finish(status, reason, code, extra = {}) {
  emit("electron_vulkan_web_parity_windows_status", status);
  emit("electron_vulkan_web_parity_windows_reason", reason);
  for (const [key, value] of Object.entries(extra)) emit(key, value);
  process.exit(code);
}

function readJson(path, label) {
  if (!path) finish("fail", `${label}-json-path-missing`, 2);
  if (!fs.existsSync(path)) finish("fail", `${label}-json-missing`, 2);
  try {
    return JSON.parse(fs.readFileSync(path, "utf8"));
  } catch (_err) {
    finish("fail", `${label}-json-malformed`, 2);
  }
}

function pixelArray(value) {
  return Array.isArray(value) ? value : [];
}

function validPositiveInteger(value) {
  return Number.isInteger(value) && value > 0;
}

function validUint32(value) {
  return Number.isInteger(value) && value >= 0 && value <= 0xFFFFFFFF;
}

function invalidPixelIndex(values) {
  for (let i = 0; i < values.length; i += 1) {
    if (!validUint32(values[i])) return i;
  }
  return -1;
}

function gpuAux(info) {
  if (info && info.gpu && info.gpu.auxAttributes) return info.gpu.auxAttributes;
  if (info && info.auxAttributes) return info.auxAttributes;
  return {};
}

function jsonSame(a, b) {
  return JSON.stringify(a || {}) === JSON.stringify(b || {});
}

function jsonObject(value) {
  return value && typeof value === "object" && !Array.isArray(value);
}

function electronVulkanProof(electron, proof, expectedPort, expectedCapturePath, expectedSourceHtmlPath, expectedSourceHtmlSha256, expectedVisualPngPath, expectedVisualPngSha256, expectedCaptureSha256) {
  const proofSource = String((proof && proof.proof_source) || "");
  const proofStatus = String((proof && proof.status) || "");
  const proofHtmlPath = String((proof && proof.html_path) || "");
  const proofHtmlSha256 = String((proof && proof.html_sha256) || "");
  const proofCapturedArgbPath = String((proof && proof.captured_argb_path) || "");
  const proofCapturedArgbSha256 = String((proof && proof.captured_argb_sha256) || "");
  const proofPngOutputPath = String((proof && proof.png_output_path) || "");
  const proofPngSha256 = String((proof && proof.png_sha256) || "");
  const proofPngWritten = proof && proof.png_written === true;
  const proofBlurOrToleranceUsed = proof ? proof.blur_or_tolerance_used : undefined;
  const proofWidth = proof ? proof.width : undefined;
  const proofHeight = proof ? proof.height : undefined;
  const proofNativeWidth = proof ? proof.native_width : undefined;
  const proofNativeHeight = proof ? proof.native_height : undefined;
  const proofDownsampled = proof ? proof.downsampled : undefined;
  const proofRemoteDebuggingPort = String((proof && proof.remote_debugging_port) || "");
  const proofCapturedArgbWritten = proof && proof.captured_argb_written === true;
  const captureSourceOk = proofSource === "tools/electron-live-bitmap/capture_html_argb.js";
  const proofStatusOk = proofStatus === "pass";
  const proofDimensionsOk = proof &&
    proofWidth === electron.width &&
    proofHeight === electron.height;
  const proofNativeDimensionsOk = proof &&
    proofNativeWidth === electron.width &&
    proofNativeHeight === electron.height;
  const proofNotDownsampled = proof && proofDownsampled === false;
  const remoteDebuggingPortOk = !expectedPort || proofRemoteDebuggingPort === expectedPort;
  const capturedArgbPathOk = !expectedCapturePath || proofCapturedArgbPath === expectedCapturePath;
  const capturedArgbSha256Ok = !expectedCaptureSha256 || proofCapturedArgbSha256 === expectedCaptureSha256;
  const htmlPathOk = !expectedSourceHtmlPath || proofHtmlPath === expectedSourceHtmlPath;
  const htmlSha256Ok = !expectedSourceHtmlSha256 || proofHtmlSha256 === expectedSourceHtmlSha256;
  const pngPathOk = !expectedVisualPngPath || proofPngOutputPath === expectedVisualPngPath;
  const pngWrittenOk = !expectedVisualPngPath || proofPngWritten;
  const pngSha256Ok = !expectedVisualPngSha256 || proofPngSha256 === expectedVisualPngSha256;
  const noBlurOrTolerance = proof && proofBlurOrToleranceUsed === false;
  const proofFeatureStatus = proof && proof.gpu_feature_status ? proof.gpu_feature_status : {};
  const electronFeatureStatus = electron && electron.gpuFeatureStatus ? electron.gpuFeatureStatus : null;
  const proofBrowserGpuInfo = jsonObject(proof && proof.browser_target_gpu_info) ? proof.browser_target_gpu_info : {};
  const electronBrowserGpuInfo = jsonObject(electron && electron.browserTargetGpuInfo) ? electron.browserTargetGpuInfo : null;
  const browserTargetGpuInfoPresent = Object.keys(proofBrowserGpuInfo).length > 0 && !proofBrowserGpuInfo.error;
  const featureStatusMatchesCapture = !electronFeatureStatus || jsonSame(proofFeatureStatus, electronFeatureStatus);
  const browserGpuInfoMatchesCapture = !electronBrowserGpuInfo || jsonSame(proofBrowserGpuInfo, electronBrowserGpuInfo);
  const featureStatus = proof && proof.gpu_feature_status
    ? proof.gpu_feature_status
    : (electron && electron.gpuFeatureStatus ? electron.gpuFeatureStatus : {});
  const browserGpuInfo = proof && proof.browser_target_gpu_info
    ? proof.browser_target_gpu_info
    : (electron && electron.browserTargetGpuInfo ? electron.browserTargetGpuInfo : {});
  const appGpuInfo = proof && proof.gpu_info
    ? proof.gpu_info
    : (electron && electron.gpuInfo ? electron.gpuInfo : {});
  const gpuInfo = browserGpuInfo && !browserGpuInfo.error ? browserGpuInfo : appGpuInfo;
  const aux = gpuAux(gpuInfo);
  const appAux = gpuAux(appGpuInfo);
  const vulkan = String(featureStatus.vulkan || "");
  const gpuCompositing = String(featureStatus.gpu_compositing || "");
  const displayType = String(aux.displayType || "");
  const glParts = String(aux.glImplementationParts || appAux.glImplementationParts || "");
  const skiaBackend = String(aux.skiaBackendType || appAux.skiaBackendType || "");
  const glRenderer = String(aux.glRenderer || appAux.glRenderer || "");
  const browserStatus = proof && proof.browser_target_gpu_info_status
    ? String(proof.browser_target_gpu_info_status)
    : (browserGpuInfo && !browserGpuInfo.error ? "pass" : "not-run");
  const hardware = aux.hardwareSupportsVulkan === true || appAux.hardwareSupportsVulkan === true;
  const mentionsVulkan = /vulkan/i.test(`${displayType} ${glParts} ${skiaBackend} ${glRenderer}`);
  const enabled = /^enabled/i.test(vulkan);
  const gpuEnabled = /^enabled/i.test(gpuCompositing);
  const browserInfoOk = browserStatus === "pass";
  const backed = proofStatusOk && captureSourceOk && htmlPathOk && htmlSha256Ok &&
    proofCapturedArgbWritten && capturedArgbPathOk && capturedArgbSha256Ok && pngPathOk && pngWrittenOk && noBlurOrTolerance &&
    pngSha256Ok && featureStatusMatchesCapture && browserGpuInfoMatchesCapture &&
    proofDimensionsOk && proofNativeDimensionsOk && proofNotDownsampled && remoteDebuggingPortOk &&
    enabled && gpuEnabled && hardware && mentionsVulkan && browserInfoOk && browserTargetGpuInfoPresent;
  let reason = "electron-vulkan-backed";
  if (!proofStatusOk) reason = "electron-proof-status-not-pass";
  else if (!captureSourceOk) reason = "electron-proof-source-invalid";
  else if (!htmlPathOk) reason = "electron-proof-html-path-mismatch";
  else if (!htmlSha256Ok) reason = "electron-proof-html-sha256-mismatch";
  else if (!proofCapturedArgbWritten) reason = "electron-proof-argb-not-written";
  else if (!capturedArgbPathOk) reason = "electron-proof-captured-argb-path-mismatch";
  else if (!capturedArgbSha256Ok) reason = "electron-proof-captured-argb-sha256-mismatch";
  else if (!pngPathOk) reason = "electron-proof-png-path-mismatch";
  else if (!pngWrittenOk) reason = "electron-proof-png-not-written";
  else if (!pngSha256Ok) reason = "electron-proof-png-sha256-mismatch";
  else if (!noBlurOrTolerance) reason = "electron-proof-tolerance-used";
  else if (!featureStatusMatchesCapture) reason = "electron-proof-gpu-feature-status-mismatch";
  else if (!browserGpuInfoMatchesCapture) reason = "electron-proof-browser-gpu-info-mismatch";
  else if (!proofDimensionsOk) reason = "electron-proof-frame-mismatch";
  else if (!proofNativeDimensionsOk) reason = "electron-proof-native-frame-mismatch";
  else if (!proofNotDownsampled) reason = "electron-proof-downsampled";
  else if (!remoteDebuggingPortOk) reason = "electron-proof-remote-debugging-port-mismatch";
  else if (!enabled) reason = `electron-vulkan-${vulkan || "unknown"}`;
  else if (!gpuEnabled) reason = "electron-gpu-compositing-disabled";
  else if (!hardware) reason = "electron-vulkan-hardware-missing";
  else if (!mentionsVulkan) reason = "electron-vulkan-metadata-missing";
  else if (!browserInfoOk || !browserTargetGpuInfoPresent) reason = "electron-browser-gpu-info-not-proven";
  return {
    status: backed ? "pass" : "fail",
    reason,
    proofSource,
    proofStatus,
    proofHtmlPath,
    proofHtmlSha256,
    proofCapturedArgbPath,
    proofCapturedArgbSha256,
    proofCapturedArgbWritten,
    proofPngOutputPath,
    proofPngSha256,
    proofPngWritten,
    proofBlurOrToleranceUsed: proofBlurOrToleranceUsed === undefined ? "" : proofBlurOrToleranceUsed,
    featureStatusMatchesCapture,
    browserGpuInfoMatchesCapture,
    proofWidth: proofWidth === undefined ? "" : proofWidth,
    proofHeight: proofHeight === undefined ? "" : proofHeight,
    proofNativeWidth: proofNativeWidth === undefined ? "" : proofNativeWidth,
    proofNativeHeight: proofNativeHeight === undefined ? "" : proofNativeHeight,
    proofDownsampled: proofDownsampled === undefined ? "" : proofDownsampled,
    proofRemoteDebuggingPort,
    vulkan,
    gpuCompositing,
    browserStatus,
    displayType,
    glParts,
    skiaBackend,
    glRenderer,
    hardware,
  };
}

if ((expectedWidthProvided && !validPositiveInteger(expectedWidth)) ||
    (expectedHeightProvided && !validPositiveInteger(expectedHeight)) ||
    (expectedArgbProvided && !validUint32(expectedArgb))) {
  finish("fail", "expected-frame-args-invalid", 2, {
    electron_vulkan_web_parity_windows_compare_expected_width: process.argv[5] || "",
    electron_vulkan_web_parity_windows_compare_expected_height: process.argv[6] || "",
    electron_vulkan_web_parity_windows_compare_expected_argb: process.argv[7] || "",
  });
}

const electron = readJson(electronPath, "electron");
const vulkan = readJson(vulkanPath, "vulkan");
const electronProof = electronProofPath ? readJson(electronProofPath, "electron-proof") : null;
const electronPixels = pixelArray(electron.pixels);
const vulkanPixels = pixelArray(vulkan.pixels);
const electronProducer = String(electron.producer || "");
const electronWidth = Number(electron.width || 0);
const electronHeight = Number(electron.height || 0);
const vulkanWidth = Number(vulkan.width || 0);
const vulkanHeight = Number(vulkan.height || 0);
const vulkanBackend = String(vulkan.backend || "");
const vulkanStatus = String(vulkan.status || "");
const vulkanReason = String(vulkan.reason || "");
const vulkanSchema = String(vulkan.schema || "");
const vulkanProducer = String(vulkan.producer || "");
const vulkanEntrypoint = String(vulkan.entrypoint || "");
const vulkanRequestedBackend = String(vulkan.requested_backend || "");
const vulkanExecutionMode = String(vulkan.execution_mode || "");
const vulkanRunId = String(vulkan.run_id || "");
const vulkanPixelCount = Number(vulkan.pixel_count || 0);

const common = {
  electron_vulkan_web_parity_windows_compare_expected_width: expectedWidth,
  electron_vulkan_web_parity_windows_compare_expected_height: expectedHeight,
  electron_vulkan_web_parity_windows_compare_expected_argb: expectedArgb,
  electron_vulkan_web_parity_windows_compare_expected_remote_debugging_port: expectedRemoteDebuggingPort,
  electron_vulkan_web_parity_windows_compare_expected_captured_argb_path: expectedCapturedArgbPath,
  electron_vulkan_web_parity_windows_compare_expected_captured_argb_sha256: expectedCapturedArgbSha256,
  electron_vulkan_web_parity_windows_compare_expected_html_path: expectedHtmlPath,
  electron_vulkan_web_parity_windows_compare_expected_html_sha256: expectedHtmlSha256,
  electron_vulkan_web_parity_windows_compare_expected_png_path: expectedPngPath,
  electron_vulkan_web_parity_windows_compare_expected_png_sha256: expectedPngSha256,
  electron_vulkan_web_parity_windows_compare_expected_vulkan_run_id: expectedVulkanRunId,
  electron_vulkan_web_parity_windows_compare_expected_vulkan_json_path: expectedVulkanJsonPath,
  electron_vulkan_web_parity_windows_compare_expected_vulkan_json_sha256: expectedVulkanJsonSha256,
  electron_vulkan_web_parity_windows_compare_electron_producer: electronProducer,
  electron_vulkan_web_parity_windows_compare_electron_width: electronWidth,
  electron_vulkan_web_parity_windows_compare_electron_height: electronHeight,
  electron_vulkan_web_parity_windows_compare_vulkan_width: vulkanWidth,
  electron_vulkan_web_parity_windows_compare_vulkan_height: vulkanHeight,
  electron_vulkan_web_parity_windows_compare_electron_pixels: electronPixels.length,
  electron_vulkan_web_parity_windows_compare_vulkan_pixels: vulkanPixels.length,
  electron_vulkan_web_parity_windows_compare_vulkan_status: vulkanStatus,
  electron_vulkan_web_parity_windows_compare_vulkan_reason: vulkanReason,
  electron_vulkan_web_parity_windows_compare_vulkan_schema: vulkanSchema,
  electron_vulkan_web_parity_windows_compare_vulkan_producer: vulkanProducer,
  electron_vulkan_web_parity_windows_compare_vulkan_entrypoint: vulkanEntrypoint,
  electron_vulkan_web_parity_windows_compare_vulkan_requested_backend: vulkanRequestedBackend,
  electron_vulkan_web_parity_windows_compare_vulkan_execution_mode: vulkanExecutionMode,
  electron_vulkan_web_parity_windows_compare_vulkan_run_id: vulkanRunId,
  electron_vulkan_web_parity_windows_compare_vulkan_backend: vulkanBackend,
  electron_vulkan_web_parity_windows_compare_vulkan_pixel_count: vulkanPixelCount,
};

if (!validPositiveInteger(electron.width) ||
    !validPositiveInteger(electron.height) ||
    !validPositiveInteger(vulkan.width) ||
    !validPositiveInteger(vulkan.height)) {
  finish("fail", "frame-metadata-invalid", 2, common);
}

if (electronProducer !== "electron-chromium-capture") {
  finish("fail", "electron-producer-not-proven", 2, common);
}

if (electronProofPath) {
  const electronProofStatus = electronVulkanProof(
    electron,
    electronProof,
    expectedRemoteDebuggingPortProvided ? expectedRemoteDebuggingPort : "",
    expectedCapturedArgbPathProvided ? expectedCapturedArgbPath : "",
    expectedHtmlPathProvided ? expectedHtmlPath : "",
    expectedHtmlSha256Provided ? expectedHtmlSha256 : "",
    expectedPngPathProvided ? expectedPngPath : "",
    expectedPngSha256Provided ? expectedPngSha256 : "",
    expectedCapturedArgbSha256Provided ? expectedCapturedArgbSha256 : ""
  );
  common.electron_vulkan_web_parity_windows_compare_electron_proof = electronProofPath;
  common.electron_vulkan_web_parity_windows_compare_electron_proof_source = electronProofStatus.proofSource;
  common.electron_vulkan_web_parity_windows_compare_electron_proof_status = electronProofStatus.proofStatus;
  common.electron_vulkan_web_parity_windows_compare_electron_proof_html_path = electronProofStatus.proofHtmlPath;
  common.electron_vulkan_web_parity_windows_compare_electron_proof_html_sha256 = electronProofStatus.proofHtmlSha256;
  common.electron_vulkan_web_parity_windows_compare_electron_proof_captured_argb_path = electronProofStatus.proofCapturedArgbPath;
  common.electron_vulkan_web_parity_windows_compare_electron_proof_captured_argb_sha256 = electronProofStatus.proofCapturedArgbSha256;
  common.electron_vulkan_web_parity_windows_compare_electron_proof_captured_argb_written = electronProofStatus.proofCapturedArgbWritten ? "true" : "false";
  common.electron_vulkan_web_parity_windows_compare_electron_proof_png_path = electronProofStatus.proofPngOutputPath;
  common.electron_vulkan_web_parity_windows_compare_electron_proof_png_sha256 = electronProofStatus.proofPngSha256;
  common.electron_vulkan_web_parity_windows_compare_electron_proof_png_written = electronProofStatus.proofPngWritten ? "true" : "false";
  common.electron_vulkan_web_parity_windows_compare_electron_proof_blur_or_tolerance_used = electronProofStatus.proofBlurOrToleranceUsed;
  common.electron_vulkan_web_parity_windows_compare_electron_proof_gpu_feature_status_matches_capture = electronProofStatus.featureStatusMatchesCapture ? "true" : "false";
  common.electron_vulkan_web_parity_windows_compare_electron_proof_browser_gpu_info_matches_capture = electronProofStatus.browserGpuInfoMatchesCapture ? "true" : "false";
  common.electron_vulkan_web_parity_windows_compare_electron_proof_width = electronProofStatus.proofWidth;
  common.electron_vulkan_web_parity_windows_compare_electron_proof_height = electronProofStatus.proofHeight;
  common.electron_vulkan_web_parity_windows_compare_electron_proof_native_width = electronProofStatus.proofNativeWidth;
  common.electron_vulkan_web_parity_windows_compare_electron_proof_native_height = electronProofStatus.proofNativeHeight;
  common.electron_vulkan_web_parity_windows_compare_electron_proof_downsampled = electronProofStatus.proofDownsampled;
  common.electron_vulkan_web_parity_windows_compare_electron_proof_remote_debugging_port = electronProofStatus.proofRemoteDebuggingPort;
  common.electron_vulkan_web_parity_windows_compare_electron_vulkan_status = electronProofStatus.status;
  common.electron_vulkan_web_parity_windows_compare_electron_vulkan_reason = electronProofStatus.reason;
  common.electron_vulkan_web_parity_windows_compare_electron_vulkan = electronProofStatus.vulkan;
  common.electron_vulkan_web_parity_windows_compare_electron_gpu_compositing = electronProofStatus.gpuCompositing;
  common.electron_vulkan_web_parity_windows_compare_electron_browser_target_gpu_info_status = electronProofStatus.browserStatus;
  common.electron_vulkan_web_parity_windows_compare_electron_display_type = electronProofStatus.displayType;
  common.electron_vulkan_web_parity_windows_compare_electron_gl_implementation_parts = electronProofStatus.glParts;
  common.electron_vulkan_web_parity_windows_compare_electron_skia_backend_type = electronProofStatus.skiaBackend;
  common.electron_vulkan_web_parity_windows_compare_electron_gl_renderer = electronProofStatus.glRenderer;
  common.electron_vulkan_web_parity_windows_compare_electron_hardware_supports_vulkan = electronProofStatus.hardware ? "true" : "false";
  if (electronProofStatus.status !== "pass") {
    finish("fail", electronProofStatus.reason, 2, common);
  }
}

if (vulkanStatus !== "pass") {
  finish("fail", "vulkan-render-status-not-pass", 2, common);
}

if (vulkanSchema !== "simple-engine2d-vulkan-parity-v1") {
  finish("fail", "vulkan-schema-not-proven", 2, common);
}

if (vulkanProducer !== "simple-engine2d-vulkan") {
  finish("fail", "vulkan-producer-not-proven", 2, common);
}

if (vulkanEntrypoint !== "src/app/test/electron_vulkan_web_parity.spl") {
  finish("fail", "vulkan-entrypoint-not-proven", 2, common);
}

if (vulkanRequestedBackend !== "vulkan") {
  finish("fail", "vulkan-requested-backend-not-proven", 2, common);
}

if (vulkanExecutionMode !== "interpret") {
  finish("fail", "vulkan-execution-mode-not-proven", 2, common);
}

if (expectedVulkanRunIdProvided && vulkanRunId !== expectedVulkanRunId) {
  finish("fail", "vulkan-run-id-mismatch", 2, common);
}

if (expectedVulkanJsonPathProvided && vulkanPath !== expectedVulkanJsonPath) {
  finish("fail", "vulkan-json-path-mismatch", 2, common);
}

if (expectedVulkanJsonSha256Provided) {
  const actualVulkanJsonSha256 = require("crypto").createHash("sha256").update(fs.readFileSync(vulkanPath)).digest("hex");
  if (actualVulkanJsonSha256 !== expectedVulkanJsonSha256) {
    finish("fail", "vulkan-json-sha256-mismatch", 2, common);
  }
}

if (vulkanBackend !== "vulkan") {
  finish("fail", "vulkan-backend-not-proven", 2, common);
}

if (electronWidth !== vulkanWidth || electronHeight !== vulkanHeight) {
  finish("fail", "frame-shape-mismatch", 2, common);
}

if ((expectedWidth > 0 && electronWidth !== expectedWidth) || (expectedHeight > 0 && electronHeight !== expectedHeight)) {
  finish("fail", "frame-size-not-requested", 2, common);
}

if (electronPixels.length === 0 || vulkanPixels.length === 0) {
  finish("fail", "empty-pixel-buffer", 2, common);
}

if (electronPixels.length !== vulkanPixels.length) {
  finish("fail", "pixel-buffer-length-mismatch", 2, common);
}

if (electronPixels.length !== electronWidth * electronHeight || vulkanPixels.length !== vulkanWidth * vulkanHeight) {
  finish("fail", "pixel-buffer-shape-mismatch", 2, common);
}

if (!validPositiveInteger(vulkan.pixel_count)) {
  finish("fail", "vulkan-pixel-count-metadata-invalid", 2, common);
}

if (vulkanPixelCount !== vulkanPixels.length) {
  finish("fail", "vulkan-pixel-count-mismatch", 2, common);
}

const invalidElectronPixel = invalidPixelIndex(electronPixels);
const invalidVulkanPixel = invalidPixelIndex(vulkanPixels);
if (invalidElectronPixel !== -1 || invalidVulkanPixel !== -1) {
  finish("fail", "pixel-buffer-values-invalid", 2, {
    ...common,
    electron_vulkan_web_parity_windows_compare_invalid_electron_pixel_index: invalidElectronPixel,
    electron_vulkan_web_parity_windows_compare_invalid_vulkan_pixel_index: invalidVulkanPixel,
  });
}

if (expectedArgbProvided) {
  for (let i = 0; i < electronPixels.length; i += 1) {
    if ((electronPixels[i] >>> 0) !== (expectedArgb >>> 0) || (vulkanPixels[i] >>> 0) !== (expectedArgb >>> 0)) {
      finish("fail", "frame-color-not-requested", 2, {
        ...common,
        electron_vulkan_web_parity_windows_compare_expected_argb: expectedArgb >>> 0,
        electron_vulkan_web_parity_windows_compare_color_mismatch_index: i,
        electron_vulkan_web_parity_windows_compare_color_electron: electronPixels[i] >>> 0,
        electron_vulkan_web_parity_windows_compare_color_vulkan: vulkanPixels[i] >>> 0,
      });
    }
  }
}

let mismatches = 0;
for (let i = 0; i < electronPixels.length; i += 1) {
  if ((electronPixels[i] >>> 0) !== (vulkanPixels[i] >>> 0)) mismatches += 1;
}

const result = {
  ...common,
  electron_vulkan_web_parity_windows_compare_px0_electron: electronPixels[0] >>> 0,
  electron_vulkan_web_parity_windows_compare_px0_vulkan: vulkanPixels[0] >>> 0,
  electron_vulkan_web_parity_windows_compare_mismatches: mismatches,
};

if (mismatches !== 0) {
  finish("fail", "pixel-mismatch", 1, result);
}

finish("pass", "pixel-exact-vulkan", 0, result);
