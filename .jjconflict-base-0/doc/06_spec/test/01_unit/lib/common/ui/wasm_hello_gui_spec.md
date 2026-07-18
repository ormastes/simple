# Wasm Hello Gui Specification

> <details>

<!-- sdn-diagram:id=wasm_hello_gui_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wasm_hello_gui_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wasm_hello_gui_spec -> std
wasm_hello_gui_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wasm_hello_gui_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wasm Hello Gui Specification

## Scenarios

### generated-WASM hello GUI artifacts

#### builds Android hello world as generated WASM without JavaScript

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hello = wasm_hello_gui_artifact_for_target(WEB_RENDER_TARGET_ANDROID_WASM)
expect(hello.validation_error).to_equal("")
expect(hello.request.js).to_equal("")
expect(hello.artifact.target).to_equal(WEB_RENDER_TARGET_ANDROID_WASM)
expect(hello.artifact.html.contains("<script>")).to_equal(false)
expect(hello.artifact.html).to_contain("Hello World")
expect(hello.artifact.html).to_contain("id='hello_image'")
expect(hello.artifact.html).to_contain("data-simple-primitives='rect,circle,line'")
expect(hello.artifact.html).to_contain("id='hello_taskbar'")
expect(hello.artifact.html).to_contain("id='hello_command_bar'")
expect(hello.artifact.binary_schema).to_equal(WEB_RENDER_WASM_SCHEMA_VERSION)
expect(hello.artifact.binary_cache_path).to_equal("build/gui/android/hello.wasm")
expect(hello.artifact.binary_command_count).to_equal(14)
expect(hello.metadata.abi).to_equal("wasm32-simple-ui-android")
```

</details>

#### builds iOS hello world as generated WASM without JavaScript

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hello = wasm_hello_gui_artifact_for_target(WEB_RENDER_TARGET_IOS_WASM)
expect(hello.validation_error).to_equal("")
expect(hello.request.viewport_w).to_equal(390)
expect(hello.request.viewport_h).to_equal(844)
expect(hello.artifact.ipc_json).to_equal("")
expect(hello.artifact.binary_cache_path).to_equal("build/gui/ios/hello.wasm")
expect(hello.metadata.abi).to_equal("wasm32-simple-ui-ios")
```

</details>

#### builds host WM and SimpleOS WM hello artifacts without JavaScript

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val host = wasm_hello_gui_artifact_for_target(WEB_RENDER_TARGET_HOST_WM_WASM)
val simpleos = wasm_hello_gui_artifact_for_target(WEB_RENDER_TARGET_SIMPLEOS_WM_WASM)

expect(host.validation_error).to_equal("")
expect(simpleos.validation_error).to_equal("")
expect(host.artifact.binary_cache_path).to_equal("build/gui/host-wm/hello.wasm")
expect(simpleos.artifact.binary_cache_path).to_equal("build/gui/simpleos-wm/hello.wasm")
expect(host.metadata.abi).to_equal("wasm32-simple-ui-host-wm")
expect(simpleos.metadata.abi).to_equal("wasm32-simple-ui-simpleos-wm")
expect(host.artifact.html.contains("<script>")).to_equal(false)
expect(simpleos.artifact.html.contains("<script>")).to_equal(false)
```

</details>

<details>
<summary>Advanced: exposes the full Android iOS host WM SimpleOS WM matrix</summary>

#### exposes the full Android iOS host WM SimpleOS WM matrix

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val artifacts = wasm_hello_gui_artifacts()
expect(artifacts.len()).to_equal(4)
expect(artifacts[0].artifact.target).to_equal(WEB_RENDER_TARGET_ANDROID_WASM)
expect(artifacts[1].artifact.target).to_equal(WEB_RENDER_TARGET_IOS_WASM)
expect(artifacts[2].artifact.target).to_equal(WEB_RENDER_TARGET_HOST_WM_WASM)
expect(artifacts[3].artifact.target).to_equal(WEB_RENDER_TARGET_SIMPLEOS_WM_WASM)
expect(artifacts[0].artifact.capability_summary).to_contain("generated_wasm")
expect(artifacts[3].artifact.capability_summary).to_contain("no_javascript")
```

</details>


</details>

#### binds hello artifacts to deterministic WASM compile plans

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val android = wasm_hello_gui_compile_plan_for_target(WEB_RENDER_TARGET_ANDROID_WASM)
val ios = wasm_hello_gui_compile_plan_for_target(WEB_RENDER_TARGET_IOS_WASM)
val summary = wasm_hello_gui_compile_plan_summary(ios)

expect(android.source_entry).to_equal("examples/06_io/ui/hello_wasm_gui.spl")
expect(android.target_triple).to_equal("wasm32-unknown-unknown")
expect(android.linker).to_equal("wasm-ld")
expect(android.output_path).to_equal("build/gui/android/hello.wasm")
expect(android.ready).to_equal(true)
expect(summary).to_contain("output=build/gui/ios/hello.wasm")
expect(summary).to_contain("abi=wasm32-simple-ui-ios")
```

</details>

#### exposes compile plans for all generated-WASM hello targets

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plans = wasm_hello_gui_compile_plans()
expect(plans.len()).to_equal(4)
expect(plans[0].target).to_equal(WEB_RENDER_TARGET_ANDROID_WASM)
expect(plans[1].target).to_equal(WEB_RENDER_TARGET_IOS_WASM)
expect(plans[2].target).to_equal(WEB_RENDER_TARGET_HOST_WM_WASM)
expect(plans[3].target).to_equal(WEB_RENDER_TARGET_SIMPLEOS_WM_WASM)
expect(plans[3].output_path).to_equal("build/gui/simpleos-wm/hello.wasm")
expect(plans[3].ready).to_equal(true)
```

</details>

#### fails closed when the WASM linker is missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wasm_hello_gui_compile_plan_for_target(WEB_RENDER_TARGET_ANDROID_WASM)
val request = wasm_hello_gui_compile_request(plan, "", "/opt/wasi", true)
val result = wasm_hello_gui_compile_result_for_request(request, false)

expect(result.status).to_equal("missing_wasm_linker")
expect(result.ready).to_equal(false)
expect(result.diagnostic).to_contain("wasm linker path")
expect(result.command_line).to_contain("--output build/gui/android/hello.wasm")
```

</details>

#### reports ready-to-invoke compile requests before artifact creation

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wasm_hello_gui_compile_plan_for_target(WEB_RENDER_TARGET_IOS_WASM)
val request = wasm_hello_gui_compile_request(plan, "/usr/bin/wasm-ld", "/opt/wasi", true)
val result = wasm_hello_gui_compile_result_for_request(request, false)
val summary = wasm_hello_gui_compile_result_summary(result)

expect(result.status).to_equal("ready_to_invoke")
expect(result.ready).to_equal(true)
expect(result.output_path).to_equal("build/gui/ios/hello.wasm")
expect(result.command_line).to_contain("simple build --target=wasm")
expect(result.command_line).to_contain("--linker /usr/bin/wasm-ld")
expect(summary).to_contain("status=ready_to_invoke")
```

</details>

#### reports compiled artifacts when the target WASM module exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wasm_hello_gui_compile_plan_for_target(WEB_RENDER_TARGET_HOST_WM_WASM)
val request = wasm_hello_gui_compile_request(plan, "/usr/bin/wasm-ld", "/opt/wasi", true)
val result = wasm_hello_gui_compile_result_for_request(request, true)

expect(result.status).to_equal("compiled_artifact_available")
expect(result.ready).to_equal(true)
expect(result.diagnostic).to_equal("")
expect(result.output_path).to_equal("build/gui/host-wm/hello.wasm")
```

</details>

#### fails closed when WASI sysroot or source entry is missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wasm_hello_gui_compile_plan_for_target(WEB_RENDER_TARGET_SIMPLEOS_WM_WASM)
val no_sysroot = wasm_hello_gui_compile_result_for_request(wasm_hello_gui_compile_request(plan, "/usr/bin/wasm-ld", "", true), false)
val no_source = wasm_hello_gui_compile_result_for_request(wasm_hello_gui_compile_request(plan, "/usr/bin/wasm-ld", "/opt/wasi", false), false)

expect(no_sysroot.status).to_equal("missing_wasi_sysroot")
expect(no_sysroot.ready).to_equal(false)
expect(no_source.status).to_equal("missing_source_entry")
expect(no_source.diagnostic).to_contain("examples/06_io/ui/hello_wasm_gui.spl")
```

</details>

#### defines no-JavaScript runtime packages for mobile and WM targets

<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val android = wasm_hello_gui_target_package_for_target(WEB_RENDER_TARGET_ANDROID_WASM)
val ios = wasm_hello_gui_target_package_for_target(WEB_RENDER_TARGET_IOS_WASM)
val host = wasm_hello_gui_target_package_for_target(WEB_RENDER_TARGET_HOST_WM_WASM)
val simpleos = wasm_hello_gui_target_package_for_target(WEB_RENDER_TARGET_SIMPLEOS_WM_WASM)
val summary = wasm_hello_gui_target_package_summary(simpleos)

expect(android.ready).to_equal(true)
expect(ios.ready).to_equal(true)
expect(host.ready).to_equal(true)
expect(simpleos.ready).to_equal(true)
expect(android.no_javascript).to_equal(true)
expect(ios.launcher_entry).to_equal("ios-native-wasm-surface")
expect(host.shell_runtime).to_equal("host-wm:no-js:wasm32-simple-ui")
expect(simpleos.shell_runtime).to_equal("simpleos-wm:no-js:wasm32-simple-ui")
expect(simpleos.event_contract).to_contain("button:hello_button:click->hello_button:clicked")
expect(simpleos.event_contract).to_contain("scroll:viewport->hello_scroll:accepted")
expect(simpleos.event_contract).to_contain("text:hello_text->hello_text:accepted")
expect(simpleos.render_contract).to_contain("button-min-height=44")
expect(simpleos.render_contract).to_contain("image=64x64")
expect(simpleos.render_contract).to_contain("primitives=rect,circle,line:128x48")
expect(simpleos.render_contract).to_contain("taskbar=hello_taskbar")
expect(simpleos.render_contract).to_contain("command_bar=hello_command_bar")
expect(summary).to_contain("launcher=simpleos-wm-native-wasm-window")
expect(summary).to_contain("no_js=true")
```

</details>

<details>
<summary>Advanced: exposes package contracts for the full target matrix</summary>

#### exposes package contracts for the full target matrix

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val packages = wasm_hello_gui_target_packages()

expect(packages.len()).to_equal(4)
expect(packages[0].platform).to_equal("android")
expect(packages[1].platform).to_equal("ios")
expect(packages[2].platform).to_equal("host-wm")
expect(packages[3].platform).to_equal("simpleos-wm")
expect(packages[0].module_path).to_equal("build/gui/android/hello.wasm")
expect(packages[3].module_path).to_equal("build/gui/simpleos-wm/hello.wasm")
expect(packages[0].blocker).to_equal("")
expect(packages[3].blocker).to_equal("")
```

</details>


</details>

#### records real compiled WASM evidence fail-closed

<details>
<summary>Executable SSpec</summary>

Runnable source: 73 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = wasm_hello_gui_compiled_artifact_evidence(
    WEB_RENDER_TARGET_SIMPLEOS_WM_WASM,
    "/tmp/hello_wasm_gui_feature.wasm",
    1906,
    "0061736d",
    1,
    false,
    true,
    true,
    true,
    true,
    true,
    true,
    true
)
val smf = wasm_hello_gui_compiled_artifact_evidence(
    WEB_RENDER_TARGET_SIMPLEOS_WM_WASM,
    "/tmp/hello_wasm_gui_cli.wasm",
    128,
    "0061736d",
    1,
    true,
    true,
    true,
    true,
    true,
    true,
    true,
    true
)
val missing_render = wasm_hello_gui_compiled_artifact_evidence(
    WEB_RENDER_TARGET_HOST_WM_WASM,
    "/tmp/hello_wasm_gui_feature.wasm",
    1906,
    "0061736d",
    1,
    false,
    true,
    true,
    false,
    true,
    true,
    true,
    true
)
val missing_events = wasm_hello_gui_compiled_artifact_evidence(
    WEB_RENDER_TARGET_HOST_WM_WASM,
    "/tmp/hello_wasm_gui_feature.wasm",
    1906,
    "0061736d",
    1,
    false,
    true,
    true,
    true,
    true,
    true,
    true,
    false
)

expect(ok.status).to_equal("compiled_wasm_verified")
expect(ok.ready).to_equal(true)
expect(ok.has_simple_app_init).to_equal(true)
expect(ok.has_simple_app_render).to_equal(true)
expect(ok.has_simple_app_event).to_equal(true)
expect(ok.diagnostic).to_equal("")
expect(smf.status).to_equal("smf_artifact_not_wasm")
expect(smf.ready).to_equal(false)
expect(missing_render.status).to_equal("missing_simple_app_render")
expect(missing_render.diagnostic).to_contain("simple_app_render")
expect(missing_events.status).to_equal("missing_event_strings")
expect(missing_events.diagnostic).to_contain("button scroll text")
```

</details>

#### verifies generated-WASM event responses without JavaScript

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = wasm_hello_gui_event_evidence(WEB_RENDER_TARGET_HOST_WM_WASM)

expect(wasm_hello_gui_event_response("click", "hello_button")).to_equal("hello_button:clicked")
expect(wasm_hello_gui_event_response("scroll", "viewport")).to_equal("hello_scroll:accepted")
expect(wasm_hello_gui_event_response("text", "hello_text")).to_equal("hello_text:accepted")
expect(wasm_hello_gui_event_response("command", "hello_command_input")).to_equal("hello_command:accepted")
expect(wasm_hello_gui_event_response("text", "wrong_text")).to_equal("hello_event:ignored")
expect(evidence.status).to_equal("event_contract_verified")
expect(evidence.ready).to_equal(true)
expect(evidence.button_ok).to_equal(true)
expect(evidence.scroll_ok).to_equal(true)
expect(evidence.text_ok).to_equal(true)
expect(evidence.ignored_ok).to_equal(true)
```

</details>

#### verifies generated-WASM GUI library surface coverage

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = wasm_hello_gui_surface_evidence_for_target(WEB_RENDER_TARGET_SIMPLEOS_WM_WASM)
val summary = wasm_hello_gui_surface_evidence_summary(evidence)

expect(evidence.status).to_equal("surface_contract_verified")
expect(evidence.ready).to_equal(true)
expect(evidence.surface_count).to_equal(8)
expect(evidence.missing_surface).to_equal("")
expect(evidence.present_surfaces).to_contain("layout")
expect(evidence.present_surfaces).to_contain("button")
expect(evidence.present_surfaces).to_contain("input")
expect(evidence.present_surfaces).to_contain("image")
expect(evidence.present_surfaces).to_contain("text")
expect(evidence.present_surfaces).to_contain("primitives")
expect(evidence.present_surfaces).to_contain("taskbar")
expect(evidence.present_surfaces).to_contain("command_bar")
expect(summary).to_contain("surfaces=layout,button,input,image,text,primitives,taskbar,command_bar")
```

</details>

#### verifies generated-WASM layout image primitive size and DPI evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val android = wasm_hello_gui_render_evidence_for_target(WEB_RENDER_TARGET_ANDROID_WASM, 1000)
val ios_hi_dpi = wasm_hello_gui_render_evidence_for_target(WEB_RENDER_TARGET_IOS_WASM, 2000)
val simpleos = wasm_hello_gui_render_evidence_for_target(WEB_RENDER_TARGET_SIMPLEOS_WM_WASM, 1000)

expect(android.status).to_equal("render_contract_verified")
expect(android.ready).to_equal(true)
expect(android.viewport_w).to_equal(412)
expect(android.viewport_h).to_equal(915)
expect(android.has_layout_marker).to_equal(true)
expect(android.has_image).to_equal(true)
expect(android.image_w).to_equal(64)
expect(android.image_h).to_equal(64)
expect(android.primitive_count).to_equal(3)
expect(android.primitive_bounds_w).to_equal(128)
expect(android.primitive_bounds_h).to_equal(48)
expect(android.min_touch_h).to_equal(44)
expect(android.command_count).to_equal(14)
expect(ios_hi_dpi.min_touch_h).to_equal(88)
expect(simpleos.viewport_w).to_equal(800)
expect(simpleos.viewport_h).to_equal(600)
```

</details>

#### verifies generated-WASM browser imports and exports before execution

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = wasm_hello_gui_default_module_contract_evidence(WEB_RENDER_TARGET_SIMPLEOS_WM_WASM)
val summary = wasm_hello_gui_module_contract_summary(evidence)

expect(evidence.status).to_equal("wasm_browser_contract_verified")
expect(evidence.ready).to_equal(true)
expect(evidence.allowed_imports).to_contain("simple_ui.present")
expect(evidence.denied_imports).to_contain("host.shell")
expect(evidence.required_exports).to_contain("spl_main")
expect(evidence.required_exports).to_contain("simple_app_event")
expect(evidence.required_exports).to_contain("simple_app_render_probe")
expect(evidence.required_exports).to_contain("simple_app_event_probe")
expect(summary).to_contain("ready=true")
```

</details>

#### rejects generated-WASM browser modules with host escapes or missing exports

<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val host_escape = wasm_hello_gui_module_contract_evidence(
    WEB_RENDER_TARGET_HOST_WM_WASM,
    ["env.memory", "simple_ui.present", "host.shell"],
    ["spl_main", "simple_app_init", "simple_app_render", "simple_app_event", "simple_app_render_probe", "simple_app_event_probe"]
)
val missing_export = wasm_hello_gui_module_contract_evidence(
    WEB_RENDER_TARGET_ANDROID_WASM,
    ["env.memory", "simple_ui.present", "simple_ui.input"],
    ["spl_main", "simple_app_init", "simple_app_render", "simple_app_event", "simple_app_render_probe"]
)
val unlisted_import = wasm_hello_gui_module_contract_evidence(
    WEB_RENDER_TARGET_IOS_WASM,
    ["env.memory", "random.unlisted"],
    ["spl_main", "simple_app_init", "simple_app_render", "simple_app_event", "simple_app_render_probe", "simple_app_event_probe"]
)

expect(host_escape.status).to_equal("wasm_import_denied")
expect(host_escape.bad_import).to_equal("host.shell")
expect(host_escape.ready).to_equal(false)
expect(missing_export.status).to_equal("wasm_export_missing")
expect(missing_export.missing_export).to_equal("simple_app_event_probe")
expect(missing_export.ready).to_equal(false)
expect(unlisted_import.status).to_equal("wasm_import_denied")
expect(unlisted_import.bad_import).to_equal("random.unlisted")
```

</details>

#### rejects generated-WASM browser modules without the Simple entrypoint

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing_entry = wasm_hello_gui_module_contract_evidence(
    WEB_RENDER_TARGET_SIMPLEOS_WM_WASM,
    ["env.memory", "simple_ui.present", "simple_ui.input"],
    ["simple_app_init", "simple_app_render", "simple_app_event", "simple_app_render_probe", "simple_app_event_probe"]
)

expect(missing_entry.status).to_equal("wasm_export_missing")
expect(missing_entry.missing_export).to_equal("spl_main")
expect(missing_entry.ready).to_equal(false)
expect(missing_entry.diagnostic).to_contain("spl_main")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/wasm_hello_gui_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- generated-WASM hello GUI artifacts

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
