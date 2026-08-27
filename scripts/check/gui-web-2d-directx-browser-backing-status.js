#!/usr/bin/env node
const fs = require("fs");

const proofPath = process.argv[2] || "";
const prefix = process.argv[3] || "browser";

function emit(k, v) {
  console.log(`${prefix}_browser_backing_${k}=${v === undefined || v === null ? "" : v}`);
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

const proofFileStatus = sourceFileStatus(proofPath);
emit("proof", proofPath);
emit("proof_file_status", proofFileStatus);

if (proofFileStatus !== "pass") {
  emit("status", proofFileStatus === "missing" ? "missing" : "fail");
  emit("reason", `proof-file-${proofFileStatus}`);
  emit("d3d11_hint_present", "false");
  emit("gpu_compositing", "");
  emit("webgl", "");
  emit("gpu_info_status", "missing");
  process.exit(0);
}

try {
  const proof = JSON.parse(fs.readFileSync(proofPath, "utf8"));
  const text = JSON.stringify(proof).toLowerCase();
  const hasD3d = text.includes("d3d11") || text.includes("direct3d") || text.includes("angle");
  const status = proof.status === "pass" && proof.blur_or_tolerance_used === false ? "pass" : "fail";
  emit("status", status);
  emit("reason", status === "pass" ? "pass" : "proof-not-pass");
  emit("d3d11_hint_present", hasD3d ? "true" : "false");
  emit("gpu_compositing", proof.gpu_feature_status && proof.gpu_feature_status.gpu_compositing || "");
  emit("webgl", proof.gpu_feature_status && proof.gpu_feature_status.webgl || "");
  emit("gpu_info_status", proof.gpu_info || proof.gpuInfo ? "present" : "missing");
} catch (_err) {
  emit("status", "invalid");
  emit("reason", "invalid-proof-json");
}
