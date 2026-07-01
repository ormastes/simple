#!/usr/bin/env node
const fs = require("fs");

const electronPath = process.argv[2] || "";
const vulkanPath = process.argv[3] || "";
const electronProofPath = process.argv[4] || "";
const expectedWidth = Number(process.argv[5] || 0);
const expectedHeight = Number(process.argv[6] || 0);
const expectedArgbProvided = process.argv.length > 7 && process.argv[7] !== "";
const expectedArgb = expectedArgbProvided ? Number(process.argv[7]) : 0;

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

function gpuAux(info) {
  if (info && info.gpu && info.gpu.auxAttributes) return info.gpu.auxAttributes;
  if (info && info.auxAttributes) return info.auxAttributes;
  return {};
}

function electronVulkanProof(electron, proof) {
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
  const hardware = Boolean(aux.hardwareSupportsVulkan || appAux.hardwareSupportsVulkan);
  const mentionsVulkan = /vulkan/i.test(`${displayType} ${glParts} ${skiaBackend} ${glRenderer}`);
  const enabled = /enabled/i.test(vulkan);
  const gpuEnabled = /enabled/i.test(gpuCompositing);
  const browserInfoOk = browserStatus === "pass";
  return {
    status: enabled && gpuEnabled && hardware && mentionsVulkan && browserInfoOk ? "pass" : "fail",
    reason: enabled && gpuEnabled && hardware && mentionsVulkan && browserInfoOk
      ? "electron-vulkan-backed"
      : (!enabled ? `electron-vulkan-${vulkan || "unknown"}` : (!gpuEnabled ? "electron-gpu-compositing-disabled" : (!hardware ? "electron-vulkan-hardware-missing" : (!mentionsVulkan ? "electron-vulkan-metadata-missing" : "electron-browser-gpu-info-not-proven")))),
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

const electron = readJson(electronPath, "electron");
const vulkan = readJson(vulkanPath, "vulkan");
const electronProof = electronProofPath ? readJson(electronProofPath, "electron-proof") : null;
const electronPixels = pixelArray(electron.pixels);
const vulkanPixels = pixelArray(vulkan.pixels);
const electronWidth = Number(electron.width || 0);
const electronHeight = Number(electron.height || 0);
const vulkanWidth = Number(vulkan.width || 0);
const vulkanHeight = Number(vulkan.height || 0);
const vulkanBackend = String(vulkan.backend || "");
const vulkanStatus = String(vulkan.status || "");
const vulkanReason = String(vulkan.reason || "");
const vulkanProducer = String(vulkan.producer || "");
const vulkanRequestedBackend = String(vulkan.requested_backend || "");
const vulkanPixelCount = Number(vulkan.pixel_count || 0);

const common = {
  electron_vulkan_web_parity_windows_compare_expected_width: expectedWidth,
  electron_vulkan_web_parity_windows_compare_expected_height: expectedHeight,
  electron_vulkan_web_parity_windows_compare_expected_argb: expectedArgb,
  electron_vulkan_web_parity_windows_compare_electron_width: electronWidth,
  electron_vulkan_web_parity_windows_compare_electron_height: electronHeight,
  electron_vulkan_web_parity_windows_compare_vulkan_width: vulkanWidth,
  electron_vulkan_web_parity_windows_compare_vulkan_height: vulkanHeight,
  electron_vulkan_web_parity_windows_compare_electron_pixels: electronPixels.length,
  electron_vulkan_web_parity_windows_compare_vulkan_pixels: vulkanPixels.length,
  electron_vulkan_web_parity_windows_compare_vulkan_status: vulkanStatus,
  electron_vulkan_web_parity_windows_compare_vulkan_reason: vulkanReason,
  electron_vulkan_web_parity_windows_compare_vulkan_producer: vulkanProducer,
  electron_vulkan_web_parity_windows_compare_vulkan_requested_backend: vulkanRequestedBackend,
  electron_vulkan_web_parity_windows_compare_vulkan_backend: vulkanBackend,
  electron_vulkan_web_parity_windows_compare_vulkan_pixel_count: vulkanPixelCount,
};

if (electronProofPath) {
  const electronProofStatus = electronVulkanProof(electron, electronProof);
  common.electron_vulkan_web_parity_windows_compare_electron_proof = electronProofPath;
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

if (vulkanProducer !== "simple-engine2d-vulkan") {
  finish("fail", "vulkan-producer-not-proven", 2, common);
}

if (vulkanRequestedBackend !== "vulkan") {
  finish("fail", "vulkan-requested-backend-not-proven", 2, common);
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

if (vulkanPixelCount !== vulkanPixels.length) {
  finish("fail", "vulkan-pixel-count-mismatch", 2, common);
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
