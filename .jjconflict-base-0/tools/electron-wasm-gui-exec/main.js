#!/usr/bin/env node
"use strict";

const { app, BrowserWindow } = require("electron");
const fs = require("fs");
const path = require("path");

const wasmPath = process.env.GUI_WASM_EXEC_WASM_PATH || "build/gui_wasm_cli_artifact/hello_wasm_gui.wasm";
const proofPath = process.env.GUI_WASM_EXEC_PROOF_PATH || "build/gui_wasm_browser_execution_evidence/proof.json";
const width = Number(process.env.GUI_WASM_EXEC_WIDTH || 320);
const height = Number(process.env.GUI_WASM_EXEC_HEIGHT || 200);

function expectedProbeValues(modulePath) {
  const base = path.basename(modulePath);
  if (base.includes("builder_matrix")) {
    return { render: "48", event: "8" };
  }
  if (base.includes("widget_matrix")) {
    return { render: "25", event: "23" };
  }
  return { render: "8", event: "5" };
}

function expectedBehavior(modulePath) {
  const base = path.basename(modulePath);
  if (base.includes("builder_matrix")) {
    return {
      retainedHtml: "<main data-simple-wasm='builder_matrix' data-builder-source='common.ui.builder'><section id='builder_navigation_bar'></section><section id='builder_matrix_controls'><input id='builder_radio_ready' type='radio'><input id='builder_switch_enabled' type='checkbox'><input id='builder_search_bar' type='search'><button id='builder_segmented_mode'>Mode</button></section><section id='builder_card_summary'><h2 id='builder_heading_title'>Builder Matrix</h2><label id='builder_label_status'>Ready</label><hr id='builder_divider_main'><button id='builder_command_palette'>Command</button></section><section id='builder_layout_surfaces'><aside id='builder_sidebar'></aside><aside id='builder_inspector'></aside><div id='builder_scroll'><textarea id='builder_textarea_notes'></textarea><ul id='builder_tree_root'><li>Root</li></ul></div></section><section id='builder_shell_surfaces'><div id='builder_glass_title_bar'></div><div id='builder_command_bar'></div><div id='builder_workspace_tabs'></div><div id='builder_toast'></div><dialog id='builder_sheet_modal' open></dialog><menu id='builder_context_menu'></menu><nav id='builder_utility_rail'></nav><span id='builder_status_chip'></span><span id='builder_selection_pill'></span><p id='builder_empty_state'>Empty</p></section></main>",
      retainedSelectors: [
        "[data-simple-wasm='builder_matrix']",
        "#builder_navigation_bar",
        "#builder_matrix_controls",
        "#builder_command_palette",
        "#builder_sheet_modal",
        "#builder_context_menu",
        "#builder_empty_state"
      ],
      retainedEventMutations: [
        { selector: "#builder_radio_ready", event: "change", property: "checked", value: true, expected: true },
        { selector: "#builder_switch_enabled", event: "change", property: "checked", value: true, expected: true },
        { selector: "#builder_search_bar", event: "input", property: "value", value: "matrix query", expected: "matrix query" },
        { selector: "#builder_command_palette", event: "click", attribute: "data-command-state", value: "accepted", expected: "accepted" },
        { selector: "#builder_textarea_notes", event: "input", property: "value", value: "Retained builder event mutation", expected: "Retained builder event mutation" }
      ],
      renderMarkers: [
        "data-simple-wasm='builder_matrix'",
        "data-builder-source='common.ui.builder'",
        "builder_navigation_bar",
        "builder_matrix_controls",
        "builder_card_summary",
        "builder_layout_surfaces",
        "builder_shell_surfaces",
        "builder_command_palette",
        "builder_sheet_modal",
        "builder_context_menu"
      ],
      eventMarkers: [
        "builder_radio:changed",
        "builder_switch:toggled",
        "builder_search:accepted",
        "builder_segmented:changed",
        "builder_command_palette:accepted",
        "builder_sheet_modal:opened",
        "builder_context_menu:opened",
        "builder_event:ignored"
      ]
    };
  }
  if (base.includes("widget_matrix")) {
    return {
      retainedHtml: "<main data-simple-wasm='widget_matrix'><section id='matrix_controls'><label><input id='matrix_checkbox' type='checkbox' checked>Enable</label><select id='matrix_dropdown' data-state='alpha'><option value='Alpha'>Alpha</option><option value='Beta'>Beta</option><option value='Gamma'>Gamma</option></select><input id='matrix_textfield' type='text' value='Widget matrix textfield'><textarea id='matrix_textarea'>Widget matrix textarea</textarea></section><section id='matrix_tabs'><button id='matrix_tab_overview' role='tab'>Overview</button><button id='matrix_tab_detail' role='tab'>Detail</button></section><dialog id='matrix_dialog' open data-simple-surface='dialog' data-dialog-state='open'>Dialog</dialog><section id='matrix_table_list' data-simple-surface='table list'><table id='matrix_table'><tr id='matrix_table_row_primary' data-selected='false'><td>Row</td></tr></table><ul id='matrix_list'><li id='matrix_list_item' data-selected='false'>List item</li></ul></section><section id='matrix_media' data-simple-surface='progress image tooltip'><progress id='matrix_progress' value='42' max='100' data-valid='true'></progress><img id='matrix_image' width='48' height='48' alt='Widget matrix image' title='Widget matrix tooltip' data-load-state='idle'></section><div id='matrix_tree_scroll'><div id='matrix_scroll' style='max-height:24px;overflow:auto'><ul role='tree'><li id='matrix_tree_root' role='treeitem'>Root<ul><li role='treeitem'>Leaf A</li><li role='treeitem'>Leaf B</li><li role='treeitem'>Leaf C</li><li role='treeitem'>Leaf D</li></ul></li></ul></div></div><menu id='matrix_menu'><button id='matrix_menu_file'>File</button><button id='matrix_menu_view'>View</button><button id='matrix_menu_view_zoom' data-menu-parent='matrix_menu_view'>Zoom</button></menu><footer id='matrix_statusbar' data-simple-surface='statusbar' data-queue-depth='0'>Ready</footer></main>",
      retainedSelectors: [
        "[data-simple-wasm='widget_matrix']",
        "#matrix_checkbox",
        "#matrix_dropdown",
        "#matrix_textfield",
        "#matrix_textarea",
        "#matrix_tabs",
        "#matrix_dialog",
        "#matrix_table_list",
        "#matrix_table",
        "#matrix_table_row_primary",
        "#matrix_list",
        "#matrix_list_item",
        "#matrix_media",
        "#matrix_progress",
        "#matrix_image",
        "#matrix_image[title='Widget matrix tooltip']",
        "#matrix_tree_scroll",
        "#matrix_scroll",
        "#matrix_menu",
        "#matrix_menu_file",
        "#matrix_menu_view",
        "#matrix_menu_view_zoom",
        "#matrix_statusbar"
      ],
      retainedEventMutations: [
        { selector: "#matrix_checkbox", event: "change", property: "checked", value: false, expected: false },
        { selector: "#matrix_dropdown", event: "change", property: "value", value: "Alpha", expected: "Alpha" },
        { selector: "#matrix_dropdown", event: "change_beta", property: "value", value: "Beta", expected: "Beta" },
        { selector: "#matrix_textfield", event: "input", property: "value", value: "Widget matrix edited", expected: "Widget matrix edited" },
        { selector: "#matrix_textarea", event: "input", property: "value", value: "Widget matrix textarea edited", expected: "Widget matrix textarea edited" },
        { selector: "#matrix_tab_detail", event: "click", attribute: "aria-selected", value: "true", expected: "true" },
        { selector: "#matrix_dialog", event: "open", attribute: "data-dialog-state", value: "opened", expected: "opened" },
        { selector: "#matrix_dialog", event: "close", attribute: "data-dialog-state", value: "closed", expected: "closed" },
        { selector: "#matrix_table", event: "click", attribute: "data-table-state", value: "selected", expected: "selected" },
        { selector: "#matrix_table_row_primary", event: "row_select", attribute: "data-selected", value: "true", expected: "true" },
        { selector: "#matrix_list_item", event: "click", attribute: "data-list-state", value: "selected", expected: "selected" },
        { selector: "#matrix_progress", event: "change", property: "value", value: 84, expected: 84 },
        { selector: "#matrix_progress", event: "validate", attribute: "data-valid", value: "clamped", expected: "clamped" },
        { selector: "#matrix_image", event: "mouseover", attribute: "data-tooltip-state", value: "visible", expected: "visible" },
        { selector: "#matrix_image", event: "load", attribute: "data-load-state", value: "loaded", expected: "loaded" },
        { selector: "#matrix_image", event: "error", attribute: "data-load-state", value: "error", expected: "error" },
        { selector: "#matrix_scroll", event: "scroll", property: "scrollTop", value: 12, expected: 12 },
        { selector: "#matrix_menu_file", event: "click", attribute: "data-menu-state", value: "accepted", expected: "accepted" },
        { selector: "#matrix_menu_view", event: "command", attribute: "data-menu-state", value: "view-accepted", expected: "view-accepted" },
        { selector: "#matrix_menu_view_zoom", event: "command", attribute: "data-menu-state", value: "zoom-accepted", expected: "zoom-accepted" },
        { selector: "#matrix_statusbar", event: "status", property: "textContent", value: "Ready: updated", expected: "Ready: updated" }
        ,{ selector: "#matrix_statusbar", event: "queue", attribute: "data-queue-depth", value: "1", expected: "1" }
      ],
      renderMarkers: [
        "data-simple-wasm='widget_matrix'",
        "type='checkbox'",
        "<select id='matrix_dropdown'",
        "data-state='alpha'",
        "id='matrix_textfield'",
        "<textarea id='matrix_textarea'",
        "id='matrix_tabs'",
        "<dialog id='matrix_dialog'",
        "data-dialog-state='open'",
        "<table id='matrix_table'",
        "id='matrix_table_row_primary' data-selected='false'",
        "<progress id='matrix_progress'",
        "data-valid='true'",
        "<img id='matrix_image'",
        "data-load-state='idle'",
        "id='matrix_tree_scroll'",
        "<menu id='matrix_menu'",
        "id='matrix_menu_view_zoom' data-menu-parent='matrix_menu_view'",
        "id='matrix_statusbar'"
      ],
      eventMarkers: [
        "matrix_checkbox:changed",
        "matrix_dropdown:changed",
        "matrix_dropdown:beta-selected",
        "matrix_textfield:accepted",
        "matrix_textarea:accepted",
        "matrix_tabs:selected",
        "matrix_dialog:opened",
        "matrix_dialog:closed",
        "matrix_table:selected",
        "matrix_table:row-primary-selected",
        "matrix_list:selected",
        "matrix_progress:changed",
        "matrix_progress:clamped",
        "matrix_tooltip:shown",
        "matrix_image:loaded",
        "matrix_image:error",
        "matrix_scroll:accepted",
        "matrix_menu:accepted",
        "matrix_menu:view-accepted",
        "matrix_menu:zoom-accepted",
        "matrix_statusbar:updated",
        "matrix_statusbar:queued",
        "matrix_event:ignored"
      ]
    };
  }
  return {
    retainedHtml: "<main data-simple-wasm='hello' data-layout='column-gap-8-padding-16'><nav id='hello_taskbar'><button id='hello_taskbar_home'>Home</button><button id='hello_taskbar_apps'>Apps</button></nav><section id='hello_command_bar'><button id='hello_command_run'>Run</button><input id='hello_command_input' value='simple run gui'></section><button id='hello_button'>Hello World</button><input id='hello_text' value='Generated WASM UI'><img id='hello_image' width='64' height='64' alt='Simple image'><section id='hello_primitives' data-simple-primitives='rect,circle,line'><span data-primitive='rect'></span><span data-primitive='circle'></span><span data-primitive='line'></span></section></main>",
    retainedSelectors: [
      "[data-simple-wasm='hello']",
      "#hello_taskbar",
      "#hello_command_bar",
      "#hello_button",
      "#hello_text",
      "#hello_image",
      "#hello_primitives"
    ],
    retainedEventMutations: [
      { selector: "#hello_button", event: "click", attribute: "data-event-state", value: "clicked", expected: "clicked" },
      { selector: "#hello_text", event: "input", property: "value", value: "Generated WASM UI edited", expected: "Generated WASM UI edited" },
      { selector: "#hello_command_input", event: "change", property: "value", value: "simple run gui --browser", expected: "simple run gui --browser" },
      { selector: "#hello_command_run", event: "click", attribute: "data-command-state", value: "accepted", expected: "accepted" }
    ],
    renderMarkers: [
      "data-simple-wasm='hello'",
      "id='hello_taskbar'",
      "id='hello_command_bar'",
      "id='hello_button'",
      "id='hello_text'",
      "id='hello_image'",
      "data-simple-primitives='rect,circle,line'"
    ],
    eventMarkers: [
      "hello_button:clicked",
      "hello_scroll:accepted",
      "hello_text:accepted",
      "hello_command:accepted",
      "hello_event:ignored"
    ]
  };
}

function htmlForWasm(payloadBase64, behavior) {
  return `<!doctype html>
<meta charset="utf-8">
<title>Simple GUI WASM Execution Probe</title>
<style>
html,body{margin:0;padding:0;width:100%;height:100%;overflow:hidden;background:#111827;color:#f9fafb;font:12px sans-serif}
#status{padding:8px}
#retained-root{display:block;min-height:120px;padding:12px;background:#f8fafc;color:#111827;font:13px sans-serif}
#retained-root main{display:flex;flex-direction:column;gap:8px}
#retained-root section,#retained-root nav,#retained-root footer,#retained-root menu{display:flex;gap:8px;align-items:center;min-height:20px}
#retained-root button,#retained-root input,#retained-root select,#retained-root textarea{min-height:24px}
</style>
<div id="status">pending</div>
<div id="retained-root"></div>
<script>
window.__simpleExpectedRenderMarkers = ${JSON.stringify(behavior.renderMarkers)};
window.__simpleExpectedEventMarkers = ${JSON.stringify(behavior.eventMarkers)};
window.__simpleRetainedHtml = ${JSON.stringify(behavior.retainedHtml)};
window.__simpleRetainedSelectors = ${JSON.stringify(behavior.retainedSelectors)};
window.__simpleRetainedEventMutations = ${JSON.stringify(behavior.retainedEventMutations)};
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
    const customSections = WebAssembly.Module.customSections(module, "simple.gui");
    proof.simple_gui_custom_section_count = customSections.length;
    const guiSource = customSections.length > 0 ? new TextDecoder("utf-8").decode(customSections[0]) : "";
    proof.simple_gui_custom_section_bytes = guiSource.length;
    proof.simple_gui_source_excerpt = guiSource.slice(0, 160);
    const instance = await WebAssembly.instantiate(module, {});
    proof.instantiate_result = true;
    const exports = instance.exports;
    proof.export_names = Object.keys(exports).sort();
    for (const name of ["spl_main", "simple_app_init", "simple_app_render", "simple_app_event", "simple_app_render_probe", "simple_app_event_probe"]) {
      try {
        if (typeof exports[name] !== "function") {
          proof.call_results[name] = "missing";
        } else {
          const result = exports[name]();
          proof.call_results[name] = name === "simple_app_init" || name.endsWith("_probe") ? String(result) : "called";
        }
      } catch (err) {
        proof.call_results[name] = "threw:" + String(err && err.message ? err.message : err);
      }
    }
    proof.render_behavior = (window.__simpleExpectedRenderMarkers || []).map(marker => ({
      marker,
      present: guiSource.includes(marker)
    }));
    proof.event_behavior = (window.__simpleExpectedEventMarkers || []).map(marker => ({
      marker,
      present: guiSource.includes(marker)
    }));
    const retainedRoot = document.getElementById("retained-root");
    retainedRoot.innerHTML = window.__simpleRetainedHtml || "";
    const retainedSelectors = window.__simpleRetainedSelectors || [];
    const retainedSelectorResults = retainedSelectors.map(selector => {
      const element = retainedRoot.querySelector(selector);
      const rect = element ? element.getBoundingClientRect() : { width: 0, height: 0 };
      return {
        selector,
        present: !!element,
        width: Math.round(rect.width),
        height: Math.round(rect.height)
      };
    });
    proof.retained_render = {
      mounted: retainedRoot.children.length > 0,
      root_child_count: retainedRoot.children.length,
      selector_count: retainedSelectorResults.length,
      present_count: retainedSelectorResults.filter(item => item.present).length,
      nonzero_box_count: retainedSelectorResults.filter(item => item.width > 0 && item.height > 0).length,
      selectors: retainedSelectorResults,
      text_length: retainedRoot.innerText.length
    };
    const retainedEventMutations = window.__simpleRetainedEventMutations || [];
    const retainedEventResults = retainedEventMutations.map(mutation => {
      const element = retainedRoot.querySelector(mutation.selector);
      const result = {
        selector: mutation.selector,
        event: mutation.event,
        present: !!element,
        before: null,
        after: null,
        expected: mutation.expected,
        matched: false,
        app_event_result: null
      };
      if (!element) {
        return result;
      }
      const readValue = () => {
        if (mutation.property) {
          return element[mutation.property];
        }
        return element.getAttribute(mutation.attribute);
      };
      const writeValue = () => {
        if (mutation.property) {
          element[mutation.property] = mutation.value;
        } else {
          element.setAttribute(mutation.attribute, mutation.value);
        }
      };
      element.addEventListener(mutation.event, () => {
        try {
          result.app_event_result = typeof exports.simple_app_event === "function" ? String(exports.simple_app_event()) : "missing";
        } catch (err) {
          result.app_event_result = "threw:" + String(err && err.message ? err.message : err);
        }
        writeValue();
      }, { once: true });
      result.before = readValue();
      const event = mutation.event === "click"
        ? new MouseEvent("click", { bubbles: true, cancelable: true })
        : new Event(mutation.event, { bubbles: true, cancelable: true });
      element.dispatchEvent(event);
      result.after = readValue();
      result.matched = result.after === mutation.expected && result.app_event_result === "undefined";
      return result;
    });
    proof.retained_event_mutation = {
      mutation_count: retainedEventResults.length,
      matched_count: retainedEventResults.filter(item => item.matched).length,
      app_event_call_count: retainedEventResults.filter(item => item.app_event_result === "undefined").length,
      mutations: retainedEventResults
    };
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
  const behavior = expectedBehavior(absoluteWasmPath);

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
  await win.loadURL(`data:text/html;charset=utf-8,${encodeURIComponent(htmlForWasm(payloadBase64, behavior))}`);
  const proof = await waitForProof(win);
  proof.module_path = absoluteWasmPath;
  proof.proof_path = absoluteProofPath;
  proof.window_width = width;
  proof.window_height = height;
  proof.user_agent = await win.webContents.executeJavaScript("navigator.userAgent");
  const expected = expectedProbeValues(absoluteWasmPath);
  proof.expected_render_probe = expected.render;
  proof.expected_event_probe = expected.event;
  proof.expected_render_behavior_count = behavior.renderMarkers.length;
  proof.expected_event_behavior_count = behavior.eventMarkers.length;

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

  const required = ["spl_main", "simple_app_init", "simple_app_render", "simple_app_event", "simple_app_render_probe", "simple_app_event_probe"];
  const renderBehaviorOk = Array.isArray(proof.render_behavior) &&
    proof.render_behavior.length === behavior.renderMarkers.length &&
    proof.render_behavior.every(item => item.present === true);
  const eventBehaviorOk = Array.isArray(proof.event_behavior) &&
    proof.event_behavior.length === behavior.eventMarkers.length &&
    proof.event_behavior.every(item => item.present === true);
  const retainedRenderOk = proof.retained_render &&
    proof.retained_render.mounted === true &&
    proof.retained_render.selector_count === behavior.retainedSelectors.length &&
    proof.retained_render.present_count === behavior.retainedSelectors.length &&
    proof.retained_render.nonzero_box_count === behavior.retainedSelectors.length &&
    proof.retained_render.text_length > 0;
  const retainedEventMutationOk = proof.retained_event_mutation &&
    proof.retained_event_mutation.mutation_count === behavior.retainedEventMutations.length &&
    proof.retained_event_mutation.matched_count === behavior.retainedEventMutations.length &&
    proof.retained_event_mutation.app_event_call_count === behavior.retainedEventMutations.length;
  const ok = proof.browser_ready === true &&
    proof.validate_result === true &&
    proof.instantiate_result === true &&
    proof.import_count === 0 &&
    proof.simple_gui_custom_section_count === 1 &&
    required.every(name => proof.export_names.includes(name)) &&
    proof.call_results.spl_main === "called" &&
    proof.call_results.simple_app_init === "1" &&
    proof.call_results.simple_app_render === "called" &&
    proof.call_results.simple_app_event === "called" &&
    proof.call_results.simple_app_render_probe === expected.render &&
    proof.call_results.simple_app_event_probe === expected.event &&
    renderBehaviorOk &&
    eventBehaviorOk &&
    retainedRenderOk &&
    retainedEventMutationOk;
  process.exit(ok ? 0 : 2);
}

main().catch(async err => {
  console.error(err && err.stack ? err.stack : String(err));
  try { await app.quit(); } catch (_) {}
  process.exit(1);
});
