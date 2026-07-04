#!/usr/bin/env node
const fs = require("fs");

const electronProofPath = process.argv[2] || "";
const electronArgbPath = process.argv[3] || "";
const chromeProofPath = process.argv[4] || "";

function emit(k, v) {
  console.log(`${k}=${v === undefined || v === null ? "" : v}`);
}

function readJson(path) {
  try {
    return path && fs.existsSync(path) ? JSON.parse(fs.readFileSync(path, "utf8")) : null;
  } catch (_err) {
    return null;
  }
}

function sourceFileStatus(path) {
  if (!path) return "unavailable";
  let stat = null;
  try {
    stat = fs.lstatSync(path);
  } catch (_err) {
    return "missing";
  }
  if (stat.isSymbolicLink()) return "symlink";
  if (!stat.isFile()) return "not-regular";
  if (stat.nlink > 1) return "hardlink";
  if (stat.size <= 0) return "empty";
  return "pass";
}

function gpuAux(info) {
  return info && info.gpu && info.gpu.auxAttributes
    ? info.gpu.auxAttributes
    : (info && info.auxAttributes ? info.auxAttributes : {});
}

const electronProof = readJson(electronProofPath);
const electronArgb = readJson(electronArgbPath);
const chrome = readJson(chromeProofPath);

const electronProofFileStatus = sourceFileStatus(electronProofPath);
const electronArgbFileStatus = sourceFileStatus(electronArgbPath);
const chromeProofFileStatus = sourceFileStatus(chromeProofPath);

const electronFeatureStatus = electronProof && electronProof.gpu_feature_status
  ? electronProof.gpu_feature_status
  : (electronArgb && electronArgb.gpuFeatureStatus ? electronArgb.gpuFeatureStatus : {});
const electronBrowserGpuInfo = electronProof && electronProof.browser_target_gpu_info
  ? electronProof.browser_target_gpu_info
  : (electronArgb && electronArgb.browserTargetGpuInfo ? electronArgb.browserTargetGpuInfo : {});
const electronAppGpuInfo = electronProof && electronProof.gpu_info
  ? electronProof.gpu_info
  : (electronArgb && electronArgb.gpuInfo ? electronArgb.gpuInfo : {});
const electronGpuInfo = electronBrowserGpuInfo && !electronBrowserGpuInfo.error ? electronBrowserGpuInfo : electronAppGpuInfo;
const electronBrowserGpuInfoStatus = electronProof && electronProof.browser_target_gpu_info_status
  ? String(electronProof.browser_target_gpu_info_status)
  : (electronBrowserGpuInfo && !electronBrowserGpuInfo.error ? "pass" : (electronBrowserGpuInfo && electronBrowserGpuInfo.error ? "fail" : "not-run"));
const electronBrowserGpuInfoReason = electronBrowserGpuInfo && electronBrowserGpuInfo.error ? String(electronBrowserGpuInfo.error) : electronBrowserGpuInfoStatus;
const electronVulkan = String(electronFeatureStatus.vulkan || "");
const electronGpuCompositing = String(electronFeatureStatus.gpu_compositing || "");
const electronAux = gpuAux(electronGpuInfo);
const electronAppAux = gpuAux(electronAppGpuInfo);
const electronDisplay = String(electronAux.displayType || "");
const electronHardware = Boolean(electronAux.hardwareSupportsVulkan || electronAppAux.hardwareSupportsVulkan);
const electronGlParts = String(electronAux.glImplementationParts || electronAppAux.glImplementationParts || "");
const electronSkiaBackend = String(electronAux.skiaBackendType || electronAppAux.skiaBackendType || "");
const electronGlRenderer = String(electronAux.glRenderer || electronAppAux.glRenderer || "");
const electronEnabled = /enabled/i.test(electronVulkan);
const electronGpuEnabled = /enabled/i.test(electronGpuCompositing);
const electronMentionsVulkan = /vulkan/i.test(`${electronDisplay} ${electronGlParts} ${electronSkiaBackend} ${electronGlRenderer}`);
const electronProofFileOk = electronProofFileStatus === "pass";
const electronStatus = electronEnabled && electronGpuEnabled && electronHardware && electronMentionsVulkan && electronProofFileOk ? "pass" : "fail";
const electronReason = electronStatus === "pass"
  ? "electron-vulkan-backed"
  : (!electronProofFileOk ? `electron-source-file-${electronProofFileStatus}` : (electronEnabled && !electronGpuEnabled ? "electron-vulkan-gpu-compositing-disabled" : (electronEnabled ? "electron-vulkan-enabled-without-angle-vulkan-proof" : `electron-vulkan-${electronVulkan || "unknown"}`)));

const chromeGpuInfo = chrome ? chrome.gpu_info : null;
const chromeFeatureStatus = chromeGpuInfo && chromeGpuInfo.gpu ? chromeGpuInfo.gpu.featureStatus || {} : {};
const chromeAux = chromeGpuInfo && chromeGpuInfo.gpu ? chromeGpuInfo.gpu.auxAttributes || {} : {};
const chromeDisplay = String(chromeAux.displayType || "");
const chromeGpuCompositing = String(chromeFeatureStatus.gpu_compositing || "");
const chromeGl = String(chromeAux.glImplementationParts || "");
const chromeSkiaBackend = String(chromeAux.skiaBackendType || "");
const chromeGlRenderer = String(chromeAux.glRenderer || "");
const chromeHardware = Boolean(chromeAux.hardwareSupportsVulkan);
const chromeGpuEnabled = /enabled/i.test(chromeGpuCompositing);
const chromeMentionsVulkan = /vulkan/i.test(`${chromeDisplay} ${chromeGl} ${chromeSkiaBackend} ${chromeGlRenderer}`);
const chromeProofFileOk = chromeProofFileStatus === "pass";
const chromeStatus = chromeGpuEnabled && chromeHardware && chromeMentionsVulkan && chromeProofFileOk ? "pass" : "fail";
const chromeReason = chromeStatus === "pass"
  ? "chrome-vulkan-backed"
  : (!chromeProofFileOk ? `chrome-source-file-${chromeProofFileStatus}` : (chromeGpuInfo ? (!chromeGpuEnabled ? "chrome-vulkan-gpu-compositing-disabled" : (chromeHardware ? "chrome-vulkan-not-proven" : "chrome-vulkan-hardware-missing")) : "chrome-gpu-info-missing"));

emit("gui_web_2d_vulkan_browser_backing_mode", "gpu-feature-status");
emit("gui_web_2d_vulkan_electron_browser_backing_source", electronProofPath);
emit("gui_web_2d_vulkan_electron_browser_backing_source_file_status", electronProofFileStatus);
emit("gui_web_2d_vulkan_electron_browser_backing_argb_source", electronArgbPath);
emit("gui_web_2d_vulkan_electron_browser_backing_argb_source_file_status", electronArgbFileStatus);
emit("gui_web_2d_vulkan_electron_browser_backing_browser_target_gpu_info_status", electronBrowserGpuInfoStatus);
emit("gui_web_2d_vulkan_electron_browser_backing_browser_target_gpu_info_reason", electronBrowserGpuInfoReason);
emit("gui_web_2d_vulkan_electron_browser_backing_status", electronStatus);
emit("gui_web_2d_vulkan_electron_browser_backing_reason", electronReason);
emit("gui_web_2d_vulkan_electron_browser_backing_vulkan", electronVulkan);
emit("gui_web_2d_vulkan_electron_browser_backing_gpu_compositing", electronGpuCompositing);
emit("gui_web_2d_vulkan_electron_browser_backing_display_type", electronDisplay);
emit("gui_web_2d_vulkan_electron_browser_backing_hardware_supports_vulkan", electronHardware ? "true" : "false");
emit("gui_web_2d_vulkan_electron_browser_backing_gl_implementation_parts", electronGlParts);
emit("gui_web_2d_vulkan_electron_browser_backing_skia_backend_type", electronSkiaBackend);
emit("gui_web_2d_vulkan_electron_browser_backing_gl_renderer", electronGlRenderer);
emit("gui_web_2d_vulkan_chrome_browser_backing_source", chromeProofPath);
emit("gui_web_2d_vulkan_chrome_browser_backing_source_file_status", chromeProofFileStatus);
emit("gui_web_2d_vulkan_chrome_browser_backing_status", chromeStatus);
emit("gui_web_2d_vulkan_chrome_browser_backing_reason", chromeReason);
emit("gui_web_2d_vulkan_chrome_browser_backing_display_type", chromeDisplay);
emit("gui_web_2d_vulkan_chrome_browser_backing_gpu_compositing", chromeGpuCompositing);
emit("gui_web_2d_vulkan_chrome_browser_backing_gl_implementation_parts", chromeGl);
emit("gui_web_2d_vulkan_chrome_browser_backing_skia_backend_type", chromeSkiaBackend);
emit("gui_web_2d_vulkan_chrome_browser_backing_gl_renderer", chromeGlRenderer);
emit("gui_web_2d_vulkan_chrome_browser_backing_hardware_supports_vulkan", chromeHardware ? "true" : "false");
emit("gui_web_2d_vulkan_browser_backing_status", electronStatus === "pass" && chromeStatus === "pass" ? "pass" : "fail");
emit("gui_web_2d_vulkan_browser_backing_reason", electronStatus === "pass" && chromeStatus === "pass" ? "pass" : `${electronReason};${chromeReason}`);
