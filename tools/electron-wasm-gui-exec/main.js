#!/usr/bin/env node
"use strict";

const { app, BrowserWindow } = require("electron");
const fs = require("fs");
const path = require("path");

const wasmPath = process.env.GUI_WASM_EXEC_WASM_PATH || "build/gui_wasm_cli_artifact/hello_wasm_gui.wasm";
const proofPath = process.env.GUI_WASM_EXEC_PROOF_PATH || "build/gui_wasm_browser_execution_evidence/proof.json";
const width = Number(process.env.GUI_WASM_EXEC_WIDTH || 320);
const height = Number(process.env.GUI_WASM_EXEC_HEIGHT || 200);

function htmlForWasm(payloadBase64) {
  return `<!doctype html>
<meta charset="utf-8">
<title>Simple GUI WASM Execution Probe</title>
<style>
html,body{margin:0;padding:0;width:100%;height:100%;overflow:hidden;background:#111827;color:#f9fafb;font:12px sans-serif}
#status{padding:8px}
</style>
<div id="status">pending</div>
<script>
(async () => {
  const proof = {
    browser_ready: false,
    validate_result: false,
    instantiate_result: false,
    import_count: 0,
    import_names: [],
    export_names: [],
    call_results: {},
    error: ""
  };
  try {
    const raw = Uint8Array.from(atob("${payloadBase64}"), c => c.charCodeAt(0));
    proof.byte_size = raw.byteLength;
    proof.validate_result = WebAssembly.validate(raw);
    const module = new WebAssembly.Module(raw);
    const imports = WebAssembly.Module.imports(module);
    proof.import_count = imports.length;
    proof.import_names = imports.map(item => item.module + "." + item.name + ":" + item.kind).sort();
    const instance = await WebAssembly.instantiate(module, {});
    proof.instantiate_result = true;
    const exports = instance.exports;
    proof.export_names = Object.keys(exports).sort();
    for (const name of ["spl_main", "simple_app_init", "simple_app_render", "simple_app_event"]) {
      try {
        if (typeof exports[name] !== "function") {
          proof.call_results[name] = "missing";
        } else {
          exports[name]();
          proof.call_results[name] = "called";
        }
      } catch (err) {
        proof.call_results[name] = "threw:" + String(err && err.message ? err.message : err);
      }
    }
    proof.browser_ready = true;
    document.getElementById("status").textContent = "pass";
  } catch (err) {
    proof.error = String(err && err.stack ? err.stack : err);
    document.getElementById("status").textContent = "fail";
  }
  window.__simpleGuiWasmProof = proof;
})();</script>`;
}

async function waitForProof(win) {
  const deadline = Date.now() + 15000;
  while (Date.now() < deadline) {
    const proof = await win.webContents.executeJavaScript("window.__simpleGuiWasmProof || null");
    if (proof) {
      return proof;
    }
    await new Promise(resolve => setTimeout(resolve, 50));
  }
  throw new Error("timed out waiting for WASM proof");
}

async function main() {
  await app.whenReady();
  const absoluteWasmPath = path.resolve(wasmPath);
  const absoluteProofPath = path.resolve(proofPath);
  const wasmBytes = fs.readFileSync(absoluteWasmPath);
  const payloadBase64 = wasmBytes.toString("base64");

  const win = new BrowserWindow({
    show: true,
    useContentSize: true,
    width,
    height,
    backgroundColor: "#111827",
    webPreferences: {
      nodeIntegration: false,
      contextIsolation: true,
      backgroundThrottling: false
    }
  });
  win.setContentSize(width, height);
  await win.loadURL(`data:text/html;charset=utf-8,${encodeURIComponent(htmlForWasm(payloadBase64))}`);
  const proof = await waitForProof(win);
  proof.module_path = absoluteWasmPath;
  proof.proof_path = absoluteProofPath;
  proof.window_width = width;
  proof.window_height = height;
  proof.user_agent = await win.webContents.executeJavaScript("navigator.userAgent");

  fs.mkdirSync(path.dirname(absoluteProofPath), { recursive: true });
  fs.writeFileSync(absoluteProofPath, JSON.stringify(proof, null, 2));
  console.log(`gui_wasm_browser_execution_proof=${absoluteProofPath}`);
  console.log(`gui_wasm_browser_execution_validate=${proof.validate_result}`);
  console.log(`gui_wasm_browser_execution_instantiate=${proof.instantiate_result}`);
  console.log(`gui_wasm_browser_execution_import_count=${proof.import_count}`);
  console.log(`gui_wasm_browser_execution_imports=${proof.import_names.join(",")}`);
  console.log(`gui_wasm_browser_execution_exports=${proof.export_names.join(",")}`);

  await win.close();
  await app.quit();

  const required = ["spl_main", "simple_app_init", "simple_app_render", "simple_app_event"];
  const ok = proof.browser_ready === true &&
    proof.validate_result === true &&
    proof.instantiate_result === true &&
    proof.import_count === 0 &&
    required.every(name => proof.export_names.includes(name) && proof.call_results[name] === "called");
  process.exit(ok ? 0 : 2);
}

main().catch(async err => {
  console.error(err && err.stack ? err.stack : String(err));
  try { await app.quit(); } catch (_) {}
  process.exit(1);
});
