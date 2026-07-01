#!/usr/bin/env node
const fs = require("fs");

const electronPath = process.argv[2] || "";
const vulkanPath = process.argv[3] || "";

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

const electron = readJson(electronPath, "electron");
const vulkan = readJson(vulkanPath, "vulkan");
const electronPixels = pixelArray(electron.pixels);
const vulkanPixels = pixelArray(vulkan.pixels);
const electronWidth = Number(electron.width || 0);
const electronHeight = Number(electron.height || 0);
const vulkanWidth = Number(vulkan.width || 0);
const vulkanHeight = Number(vulkan.height || 0);
const vulkanBackend = String(vulkan.backend || "");

const common = {
  electron_vulkan_web_parity_windows_compare_electron_width: electronWidth,
  electron_vulkan_web_parity_windows_compare_electron_height: electronHeight,
  electron_vulkan_web_parity_windows_compare_vulkan_width: vulkanWidth,
  electron_vulkan_web_parity_windows_compare_vulkan_height: vulkanHeight,
  electron_vulkan_web_parity_windows_compare_electron_pixels: electronPixels.length,
  electron_vulkan_web_parity_windows_compare_vulkan_pixels: vulkanPixels.length,
  electron_vulkan_web_parity_windows_compare_vulkan_backend: vulkanBackend,
};

if (vulkanBackend !== "vulkan") {
  finish("fail", "vulkan-backend-not-proven", 2, common);
}

if (electronWidth !== vulkanWidth || electronHeight !== vulkanHeight) {
  finish("fail", "frame-shape-mismatch", 2, common);
}

if (electronPixels.length === 0 || vulkanPixels.length === 0) {
  finish("fail", "empty-pixel-buffer", 2, common);
}

if (electronPixels.length !== vulkanPixels.length) {
  finish("fail", "pixel-buffer-length-mismatch", 2, common);
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
