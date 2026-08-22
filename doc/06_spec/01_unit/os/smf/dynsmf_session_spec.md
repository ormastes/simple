# dynSMF Session Specification

> Verifies the dynsmf session behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 36 | 36 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# dynSMF Session Specification

Verifies the dynsmf session behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Requirements | doc/02_requirements/nfr/low_dependency_ui_dynsmf.md |
| Plan | doc/03_plan/sys_test/low_dependency_ui_dynsmf_dynsmf_session.md |
| Design | doc/05_design/low_dependency_ui_dynsmf.md |
| Research | doc/01_research/local/low_dependency_ui_dynsmf.md |
| Source | `test/01_unit/os/smf/dynsmf_session_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the dynsmf session behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### dynSMF manifest

#### opens the one validated byte snapshot even if the path backing changes later

- Verify: opens the one validated byte snapshot even if the path backing changes later
   - Expected: opened.success is true
   - Expected: opened.handle_id equals `41)  # oracle: pinned constant asserted by this scenario`
   - Expected: replaced_status.ready is false
   - Expected: replaced_open.success is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: opens the one validated byte snapshot even if the path backing changes later")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val entry = DynSmfManifestEntry(id: "snapshot", path: "build/dynsmf/snapshot.smf", source_module: "test.snapshot", artifact_kind: "precompiled_smf", abi_version: "1", default_autoload: false, exports: [])
val captured = spec_stub_honesty_padded_bytes()

# Represents an attacker replacing/truncating the pathname after the
# capture. Checked open must consume captured, never this later view.
val replaced: [u8] = [0, 0, 0, 0]
val replaced_status = dynsmf_artifact_status_from_bytes(entry, true, replaced)
val request = DynLoadRequest.lazy(entry.id, entry.path, "snapshot-test")

file_write(dynsmf_abi_path(entry.path), entry.abi_version)
val opened = dynsmf_open_captured_bytes(entry, request, 41, true, captured)
val replaced_open = dynsmf_open_captured_bytes(entry, request, 42, true, replaced)
file_delete(dynsmf_abi_path(entry.path))
expect(opened.success).to_equal(true)
expect(opened.handle_id).to_equal(41)  # oracle: pinned constant asserted by this scenario
expect(replaced_status.ready).to_equal(false)
expect(replaced_open.success).to_equal(false)
```

</details>

#### rejects a forged snapshot path without reopening files

- Verify: rejects a forged snapshot path without reopening files
   - Expected: dynsmf_open_captured_bytes(entry, request, 43, true, captured).error_msg equals `artifact snapshot path mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: rejects a forged snapshot path without reopening files")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val entry = DynSmfManifestEntry(id: "snapshot", path: "build/dynsmf/snapshot.smf", source_module: "test.snapshot", artifact_kind: "precompiled_smf", abi_version: "1", default_autoload: false, exports: [])
val captured: [u8] = [83, 77, 70, 0]
val request = DynLoadRequest.lazy(entry.id, "build/dynsmf/other.smf", "snapshot-test")
expect(dynsmf_open_captured_bytes(entry, request, 43, true, captured).error_msg).to_equal("artifact snapshot path mismatch")
```

</details>

#### keeps checked session loading to one artifact read and a byte-consuming open

- Verify: keeps checked session loading to one artifact read and a byte-consuming open
   - Expected: capture_source.split("rt_file_read_bytes(path)").len() - 1 equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: session_source does not contain `smf_dlopen_checked`
   - Expected: session_source contains `smf_dlopen_bytes(req, next_handle, snapshot.data)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: keeps checked session loading to one artifact read and a byte-consuming open")
val capture_source = file_read_text("src/os/smf/dynsmf_snapshot.spl") ?? ""
val session_source = file_read_text("src/os/smf/dynsmf_session.spl") ?? ""
expect(capture_source.split("rt_file_read_bytes(path)").len() - 1).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(session_source.contains("smf_dlopen_checked")).to_equal(false)
expect(session_source.contains("smf_dlopen_bytes(req, next_handle, snapshot.data)")).to_equal(true)
```

</details>

#### declares all requested stdlib-like library ids

- Verify: declares all requested stdlib-like library ids
   - Expected: manifest[0].id equals `file_io`
   - Expected: manifest[1].id equals `net_io`
   - Expected: manifest[2].id equals `render2d`
   - Expected: manifest[3].id equals `web_renderer`
   - Expected: manifest[4].id equals `gui_renderer`
   - Expected: manifest[5].id equals `tui_renderer`
   - Expected: manifest[6].id equals `ui_html`
   - Expected: manifest[7].id equals `mcp_diag_tools`
   - Expected: manifest[8].id equals `fmt_tool`
   - Expected: manifest[9].id equals `lint_tool`
   - Expected: manifest[10].id equals `fix_tool`
   - Expected: manifest[11].id equals `todo_scan`
   - Expected: manifest.len() equals `12)  # oracle: pinned constant asserted by this scenario`
   - Expected: dynsmf_manifest_all_precompiled(manifest) is true
   - Expected: manifest[0].artifact_kind equals `precompiled_smf`
   - Expected: manifest[0].default_autoload is false
   - Expected: manifest[5].default_autoload is false
   - Expected: manifest[6].default_autoload is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: declares all requested stdlib-like library ids")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val manifest = dynsmf_default_manifest()
expect(manifest[0].id).to_equal("file_io")
expect(manifest[1].id).to_equal("net_io")
expect(manifest[2].id).to_equal("render2d")
expect(manifest[3].id).to_equal("web_renderer")
expect(manifest[4].id).to_equal("gui_renderer")
expect(manifest[5].id).to_equal("tui_renderer")
expect(manifest[6].id).to_equal("ui_html")
expect(manifest[7].id).to_equal("mcp_diag_tools")
expect(manifest[8].id).to_equal("fmt_tool")
expect(manifest[9].id).to_equal("lint_tool")
expect(manifest[10].id).to_equal("fix_tool")
expect(manifest[11].id).to_equal("todo_scan")
expect(manifest.len()).to_equal(12)  # oracle: pinned constant asserted by this scenario
expect(dynsmf_manifest_all_precompiled(manifest)).to_equal(true)
expect(manifest[0].artifact_kind).to_equal("precompiled_smf")
# Demand-load policy (perf program 2026-08-10): no manifest entry is
# autoloaded at startup; capabilities load on first use.
expect(manifest[0].default_autoload).to_equal(false)
expect(manifest[5].default_autoload).to_equal(false)
expect(manifest[6].default_autoload).to_equal(false)
```

</details>

#### gates the 5 new toolchain entries out of default autoload (on-demand only)

- Verify: gates the 5 new toolchain entries out of default autoload (on-demand only)
   - Expected: manifest[7].default_autoload is false
   - Expected: manifest[8].default_autoload is false
   - Expected: manifest[9].default_autoload is false
   - Expected: manifest[10].default_autoload is false
   - Expected: manifest[11].default_autoload is false
   - Expected: manifest[7].artifact_kind equals `precompiled_smf`
   - Expected: manifest[7].abi_version equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: gates the 5 new toolchain entries out of default autoload (on-demand only)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val manifest = dynsmf_default_manifest()
expect(manifest[7].default_autoload).to_equal(false)
expect(manifest[8].default_autoload).to_equal(false)
expect(manifest[9].default_autoload).to_equal(false)
expect(manifest[10].default_autoload).to_equal(false)
expect(manifest[11].default_autoload).to_equal(false)
expect(manifest[7].artifact_kind).to_equal("precompiled_smf")
expect(manifest[7].abi_version).to_equal("1")
```

</details>

#### creates deterministic compile plans for all precompiled artifacts

- Verify: creates deterministic compile plans for all precompiled artifacts
   - Expected: plans.len() equals `12)  # oracle: pinned constant asserted by this scenario`
   - Expected: dynsmf_build_plans_ready(plans) is true
   - Expected: plans[0].source_path equals `src/lib/nogc_sync_mut/io/file.spl`
   - Expected: plans[0].command equals `bin/simple compile src/lib/nogc_sync_mut/io/file.spl -o build/dynsmf/file_io.smf`
   - Expected: plans[2].source_path equals `src/lib/gc_async_mut/gpu/engine2d/backend_lane.spl`
   - Expected: plans[3].source_path equals `src/app/ui.render/html_widgets.spl`
   - Expected: plans[5].output_path equals `build/dynsmf/tui_renderer.smf`
   - Expected: plans[6].source_path equals `src/lib/common/ui/html_ui/dynsmf_entry.spl`
   - Expected: plans[6].output_path equals `build/dynsmf/ui_html.smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: creates deterministic compile plans for all precompiled artifacts")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val manifest = dynsmf_default_manifest()
val plans = dynsmf_build_plans(manifest)
expect(plans.len()).to_equal(12)  # oracle: pinned constant asserted by this scenario
expect(dynsmf_build_plans_ready(plans)).to_equal(true)
expect(plans[0].source_path).to_equal("src/lib/nogc_sync_mut/io/file.spl")
expect(plans[0].command).to_equal("bin/simple compile src/lib/nogc_sync_mut/io/file.spl -o build/dynsmf/file_io.smf")
expect(plans[2].source_path).to_equal("src/lib/gc_async_mut/gpu/engine2d/backend_lane.spl")
expect(plans[3].source_path).to_equal("src/app/ui.render/html_widgets.spl")
expect(plans[5].output_path).to_equal("build/dynsmf/tui_renderer.smf")
expect(plans[6].source_path).to_equal("src/lib/common/ui/html_ui/dynsmf_entry.spl")
expect(plans[6].output_path).to_equal("build/dynsmf/ui_html.smf")
```

</details>

#### creates ready build plans for the 5 new on-demand toolchain entries

- Verify: creates ready build plans for the 5 new on-demand toolchain entries
   - Expected: plans[7].library_id equals `mcp_diag_tools`
   - Expected: plans[7].source_path equals `src/app/mcp/main_lazy_diag_tools.spl`
   - Expected: plans[7].output_path equals `build/dynsmf/mcp_diag_tools.smf`
   - Expected: plans[7].status equals `ready`
   - Expected: plans[8].library_id equals `fmt_tool`
   - Expected: plans[8].source_path equals `src/compiler/90.tools/formatter/main.spl`
   - Expected: plans[8].command equals `bin/simple compile src/compiler/90.tools/formatter/main.spl -o build/dynsmf/f... (full value in folded executable source)`
   - Expected: plans[8].status equals `ready`
   - Expected: plans[9].library_id equals `lint_tool`
   - Expected: plans[9].source_path equals `src/compiler/90.tools/lint/main.spl`
   - Expected: plans[9].output_path equals `build/dynsmf/lint_tool.smf`
   - Expected: plans[9].status equals `ready`
   - Expected: plans[10].library_id equals `fix_tool`
   - Expected: plans[10].source_path equals `src/compiler/90.tools/fix/main.spl`
   - Expected: plans[10].output_path equals `build/dynsmf/fix_tool.smf`
   - Expected: plans[10].status equals `ready`
   - Expected: plans[11].library_id equals `todo_scan`
   - Expected: plans[11].source_path equals `src/app/todo_scan/main.spl`
   - Expected: plans[11].command equals `bin/simple compile src/app/todo_scan/main.spl -o build/dynsmf/todo_scan.smf`
   - Expected: plans[11].status equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: creates ready build plans for the 5 new on-demand toolchain entries")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val manifest = dynsmf_default_manifest()
val plans = dynsmf_build_plans(manifest)
expect(plans[7].library_id).to_equal("mcp_diag_tools")
expect(plans[7].source_path).to_equal("src/app/mcp/main_lazy_diag_tools.spl")
expect(plans[7].output_path).to_equal("build/dynsmf/mcp_diag_tools.smf")
expect(plans[7].status).to_equal("ready")
expect(plans[8].library_id).to_equal("fmt_tool")
expect(plans[8].source_path).to_equal("src/compiler/90.tools/formatter/main.spl")
expect(plans[8].command).to_equal("bin/simple compile src/compiler/90.tools/formatter/main.spl -o build/dynsmf/fmt_tool.smf")
expect(plans[8].status).to_equal("ready")
expect(plans[9].library_id).to_equal("lint_tool")
expect(plans[9].source_path).to_equal("src/compiler/90.tools/lint/main.spl")
expect(plans[9].output_path).to_equal("build/dynsmf/lint_tool.smf")
expect(plans[9].status).to_equal("ready")
expect(plans[10].library_id).to_equal("fix_tool")
expect(plans[10].source_path).to_equal("src/compiler/90.tools/fix/main.spl")
expect(plans[10].output_path).to_equal("build/dynsmf/fix_tool.smf")
expect(plans[10].status).to_equal("ready")
expect(plans[11].library_id).to_equal("todo_scan")
expect(plans[11].source_path).to_equal("src/app/todo_scan/main.spl")
expect(plans[11].command).to_equal("bin/simple compile src/app/todo_scan/main.spl -o build/dynsmf/todo_scan.smf")
expect(plans[11].status).to_equal("ready")
```

</details>

#### records general background compile evidence for non-gui and gui artifacts

- Verify: records general background compile evidence for non-gui and gui artifacts
   - Expected: session.evidence.len() equals `5)  # oracle: pinned constant asserted by this scenario`
   - Expected: session.evidence[0].library_id equals `file_io`
   - Expected: session.evidence[0].action equals `compile_background`
   - Expected: session.evidence[0].status equals `queued`
   - Expected: session.evidence[1].library_id equals `net_io`
   - Expected: session.evidence[1].status equals `skipped`
   - Expected: session.evidence[1].reason equals `disabled`
   - Expected: session.evidence[2].library_id equals `bad`
   - Expected: session.evidence[2].status equals `failed`
   - Expected: session.evidence[2].reason equals `invalid_unknown_source`
   - Expected: session.evidence[3].library_id equals `gui_renderer`
   - Expected: session.evidence[3].status equals `queued`
   - Expected: session.evidence[4].library_id equals `render2d`
   - Expected: session.evidence[4].status equals `skipped`
   - Expected: session.evidence[4].reason equals `artifact_ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: records general background compile evidence for non-gui and gui artifacts")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val manifest = [
    DynSmfManifestEntry(id: "file_io", path: "build/dynsmf/bg_file_io_missing.smf", source_module: "std.io", artifact_kind: "precompiled_smf", abi_version: "1", default_autoload: true, exports: ["open"]),
    DynSmfManifestEntry(id: "net_io", path: "build/dynsmf/bg_net_io_missing.smf", source_module: "std.net", artifact_kind: "precompiled_smf", abi_version: "1", default_autoload: true, exports: ["connect"]),
    DynSmfManifestEntry(id: "bad", path: "build/dynsmf/bg_bad.smf", source_module: "std.bad", artifact_kind: "precompiled_smf", abi_version: "1", default_autoload: true, exports: []),
    DynSmfManifestEntry(id: "gui_renderer", path: "build/dynsmf/bg_gui_renderer_missing.smf", source_module: "app.ui.web.backend", artifact_kind: "precompiled_smf", abi_version: "1", default_autoload: true, exports: ["render_gui"]),
    DynSmfManifestEntry(id: "render2d", path: "build/dynsmf/bg_render2d_ready.smf", source_module: "std.render2d", artifact_kind: "precompiled_smf", abi_version: "1", default_autoload: true, exports: ["draw"])
]
val statuses = [
    DynSmfArtifactStatus(library_id: "file_io", path: "build/dynsmf/bg_file_io_missing.smf", ready: false, reason: "missing_file", byte_count: 0, magic_hex: "short"),
    DynSmfArtifactStatus(library_id: "net_io", path: "build/dynsmf/bg_net_io_missing.smf", ready: false, reason: "missing_file", byte_count: 0, magic_hex: "short"),
    DynSmfArtifactStatus(library_id: "bad", path: "build/dynsmf/bg_bad.smf", ready: false, reason: "missing_file", byte_count: 0, magic_hex: "short"),
    DynSmfArtifactStatus(library_id: "gui_renderer", path: "build/dynsmf/bg_gui_renderer_missing.smf", ready: false, reason: "missing_file", byte_count: 0, magic_hex: "short"),
    DynSmfArtifactStatus(library_id: "render2d", path: "build/dynsmf/bg_render2d_ready.smf", ready: true, reason: "smf_artifact_ready", byte_count: 8, magic_hex: "534d4600")
]
val policy = dynsmf_policy_from_args_env(["--disable-dynsmf=net_io"], "", "")
val session = dynsmf_session_request_background_compiles_from_statuses(dynsmf_session_new("background", policy), manifest, statuses, true, true)
expect(session.evidence.len()).to_equal(5)  # oracle: pinned constant asserted by this scenario
expect(session.evidence[0].library_id).to_equal("file_io")
expect(session.evidence[0].action).to_equal("compile_background")
expect(session.evidence[0].status).to_equal("queued")
expect(session.evidence[0].reason).to_contain("bin/simple compile src/lib/nogc_sync_mut/io/file.spl")
expect(session.evidence[1].library_id).to_equal("net_io")
expect(session.evidence[1].status).to_equal("skipped")
expect(session.evidence[1].reason).to_equal("disabled")
expect(session.evidence[2].library_id).to_equal("bad")
expect(session.evidence[2].status).to_equal("failed")
expect(session.evidence[2].reason).to_equal("invalid_unknown_source")
expect(session.evidence[3].library_id).to_equal("gui_renderer")
expect(session.evidence[3].status).to_equal("queued")
expect(session.evidence[3].reason).to_contain("src/app/ui.web/backend.spl")
expect(session.evidence[4].library_id).to_equal("render2d")
expect(session.evidence[4].status).to_equal("skipped")
expect(session.evidence[4].reason).to_equal("artifact_ready")
```

</details>

#### validates precompiled SMF artifact bytes without filesystem dependency

- Verify: validates precompiled SMF artifact bytes without filesystem dependency
   - Expected: ready.ready is true
   - Expected: ready.reason equals `smf_artifact_ready`
   - Expected: ready.byte_count equals `6)  # oracle: pinned constant asserted by this scenario`
   - Expected: ready.magic_hex equals `534d4600`
   - Expected: short.ready is false
   - Expected: short.reason equals `too_short`
   - Expected: invalid.ready is false
   - Expected: invalid.reason equals `invalid_magic`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: validates precompiled SMF artifact bytes without filesystem dependency")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val entry = dynsmf_default_manifest()[0]
val ready = dynsmf_artifact_status_from_bytes(entry, true, [83, 77, 70, 0, 1, 2])
expect(ready.ready).to_equal(true)
expect(ready.reason).to_equal("smf_artifact_ready")
expect(ready.byte_count).to_equal(6)  # oracle: pinned constant asserted by this scenario
expect(ready.magic_hex).to_equal("534d4600")

val short = dynsmf_artifact_status_from_bytes(entry, true, [83, 77, 70])
expect(short.ready).to_equal(false)
expect(short.reason).to_equal("too_short")

val invalid = dynsmf_artifact_status_from_bytes(entry, true, [0, 77, 70, 0])
expect(invalid.ready).to_equal(false)
expect(invalid.reason).to_equal("invalid_magic")
```

</details>

#### reports non-precompiled or missing artifacts as not ready

- Verify: reports non-precompiled or missing artifacts as not ready
   - Expected: not_precompiled.ready is false
   - Expected: not_precompiled.reason equals `not_precompiled_smf`
   - Expected: path_status.ready is false
   - Expected: path_status.reason equals `missing_path`
   - Expected: missing_file.ready is false
   - Expected: missing_file.reason equals `missing_file`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: reports non-precompiled or missing artifacts as not ready")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val base = dynsmf_default_manifest()[0]
val wrong_kind = DynSmfManifestEntry(id: "bad", path: "build/dynsmf/bad.smf", source_module: "std.bad", artifact_kind: "source", abi_version: "1", default_autoload: true, exports: [])
val not_precompiled = dynsmf_artifact_status_from_bytes(wrong_kind, true, [83, 77, 70, 0])
expect(not_precompiled.ready).to_equal(false)
expect(not_precompiled.reason).to_equal("not_precompiled_smf")

val missing_path = DynSmfManifestEntry(id: base.id, path: "", source_module: base.source_module, artifact_kind: base.artifact_kind, abi_version: base.abi_version, default_autoload: base.default_autoload, exports: base.exports)
val path_status = dynsmf_artifact_status_from_bytes(missing_path, true, [83, 77, 70, 0])
expect(path_status.ready).to_equal(false)
expect(path_status.reason).to_equal("missing_path")

val missing_file = dynsmf_artifact_status_from_bytes(base, false, [])
expect(missing_file.ready).to_equal(false)
expect(missing_file.reason).to_equal("missing_file")
```

</details>

### dynSMF policy

#### supports skip all from args

- Verify: supports skip all from args
   - Expected: policy.disabled_all is true
   - Expected: policy.source equals `arg:--no-dynsmf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: supports skip all from args")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val policy = dynsmf_policy_from_args_env(["--no-dynsmf"], "", "")
expect(policy.disabled_all).to_equal(true)
expect(policy.source).to_equal("arg:--no-dynsmf")
```

</details>

#### supports skip all from env

- Verify: supports skip all from env
   - Expected: policy.disabled_all is true
   - Expected: policy.source equals `env:SIMPLE_DYNSMF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: supports skip all from env")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val policy = dynsmf_policy_from_args_env([], "0", "")
expect(policy.disabled_all).to_equal(true)
expect(policy.source).to_equal("env:SIMPLE_DYNSMF")
```

</details>

#### supports per-id disable from args

- Verify: supports per-id disable from args
   - Expected: dynsmf_id_disabled(policy, "web_renderer") is true
   - Expected: dynsmf_id_disabled(policy, "tui_renderer") is true
   - Expected: dynsmf_id_disabled(policy, "net_io") is false
   - Expected: policy.source equals `arg:--disable-dynsmf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: supports per-id disable from args")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val policy = dynsmf_policy_from_args_env(["--disable-dynsmf=web_renderer,tui_renderer"], "", "")
expect(dynsmf_id_disabled(policy, "web_renderer")).to_equal(true)
expect(dynsmf_id_disabled(policy, "tui_renderer")).to_equal(true)
expect(dynsmf_id_disabled(policy, "net_io")).to_equal(false)
expect(policy.source).to_equal("arg:--disable-dynsmf")
```

</details>

#### supports per-id disable from env

- Verify: supports per-id disable from env
   - Expected: dynsmf_id_disabled(policy, "web_renderer") is true
   - Expected: dynsmf_id_disabled(policy, "tui_renderer") is true
   - Expected: dynsmf_id_disabled(policy, "file_io") is false
   - Expected: policy.source equals `env:SIMPLE_DYNSMF_DISABLE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: supports per-id disable from env")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val policy = dynsmf_policy_from_args_env([], "", "web_renderer,tui_renderer")
expect(dynsmf_id_disabled(policy, "web_renderer")).to_equal(true)
expect(dynsmf_id_disabled(policy, "tui_renderer")).to_equal(true)
expect(dynsmf_id_disabled(policy, "file_io")).to_equal(false)
expect(policy.source).to_equal("env:SIMPLE_DYNSMF_DISABLE")
```

</details>

### dynSMF session lifecycle

#### autoloads tui_renderer and records evidence

- Verify: autoloads tui_renderer and records evidence
   - Expected: session.loaded.len() equals `7)  # oracle: pinned constant asserted by this scenario`
   - Expected: session.loaded[0].id equals `file_io`
   - Expected: session.loaded[5].id equals `tui_renderer`
   - Expected: session.loaded[6].id equals `ui_html`
   - Expected: session.evidence[0].action equals `load`
   - Expected: session.evidence[0].status equals `loaded`
   - Expected: session.evidence[0].reason equals `smf_dlopen`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: autoloads tui_renderer and records evidence")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val manifest = eager_default_manifest()
val session = dynsmf_session_autoload(dynsmf_session_new("test", dynsmf_policy_default()), manifest)
expect(session.loaded.len()).to_equal(7)  # oracle: pinned constant asserted by this scenario
expect(session.loaded[0].id).to_equal("file_io")
expect(session.loaded[5].id).to_equal("tui_renderer")
expect(session.loaded[6].id).to_equal("ui_html")
expect(session.evidence[0].action).to_equal("load")
expect(session.evidence[0].status).to_equal("loaded")
expect(session.evidence[0].reason).to_equal("smf_dlopen")
expect(session.evidence[0].to_text()).to_contain("default:loaded")
```

</details>

#### records skip evidence when tui_renderer is disabled while loading other defaults

- Verify: records skip evidence when tui_renderer is disabled while loading other defaults
   - Expected: session.loaded.len() equals `6)  # oracle: pinned constant asserted by this scenario`
   - Expected: session.loaded[0].id equals `file_io`
   - Expected: session.evidence[5].library_id equals `tui_renderer`
   - Expected: session.evidence[5].action equals `skip`
   - Expected: session.evidence[5].reason equals `disabled`
   - Expected: session.evidence[6].library_id equals `ui_html`
   - Expected: session.evidence[6].action equals `load`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: records skip evidence when tui_renderer is disabled while loading other defaults")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val manifest = eager_default_manifest()
val policy = dynsmf_policy_from_args_env(["--disable-dynsmf=tui_renderer"], "", "")
val session = dynsmf_session_autoload(dynsmf_session_new("test", policy), manifest)
expect(session.loaded.len()).to_equal(6)  # oracle: pinned constant asserted by this scenario
expect(session.loaded[0].id).to_equal("file_io")
expect(session.evidence[5].library_id).to_equal("tui_renderer")
expect(session.evidence[5].action).to_equal("skip")
expect(session.evidence[5].reason).to_equal("disabled")
expect(session.evidence[6].library_id).to_equal("ui_html")
expect(session.evidence[6].action).to_equal("load")
```

</details>

#### records skip evidence for every default when all dynSMF loading is disabled

- Verify: records skip evidence for every default when all dynSMF loading is disabled
   - Expected: session.loaded.len() equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: session.evidence.len() equals `7)  # oracle: pinned constant asserted by this scenario`
   - Expected: session.evidence[0].action equals `skip`
   - Expected: session.evidence[5].library_id equals `tui_renderer`
   - Expected: session.evidence[5].policy_source equals `arg:--no-dynsmf`
   - Expected: session.evidence[6].library_id equals `ui_html`
   - Expected: session.evidence[6].action equals `skip`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: records skip evidence for every default when all dynSMF loading is disabled")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val manifest = eager_default_manifest()
val policy = dynsmf_policy_from_args_env(["--no-dynsmf"], "", "")
val session = dynsmf_session_autoload(dynsmf_session_new("test", policy), manifest)
expect(session.loaded.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(session.evidence.len()).to_equal(7)  # oracle: pinned constant asserted by this scenario
expect(session.evidence[0].action).to_equal("skip")
expect(session.evidence[5].library_id).to_equal("tui_renderer")
expect(session.evidence[5].policy_source).to_equal("arg:--no-dynsmf")
expect(session.evidence[6].library_id).to_equal("ui_html")
expect(session.evidence[6].action).to_equal("skip")
```

</details>

#### checked loading fails before dlopen when the artifact file is missing

- Verify: checked loading fails before dlopen when the artifact file is missing
   - Expected: session.loaded.len() equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: session.evidence.len() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: session.evidence[0].status equals `failed`
   - Expected: session.evidence[0].reason equals `artifact_missing_file`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: checked loading fails before dlopen when the artifact file is missing")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val manifest = [
    DynSmfManifestEntry(id: "missing", path: "build/dynsmf/does_not_exist_for_dynsmf_session_spec.smf", source_module: "std.missing", artifact_kind: "precompiled_smf", abi_version: "1", default_autoload: true, exports: ["open"])
]
val session = dynsmf_session_load_checked(dynsmf_session_new("checked", dynsmf_policy_default()), manifest, "missing")
expect(session.loaded.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(session.evidence.len()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(session.evidence[0].status).to_equal("failed")
expect(session.evidence[0].reason).to_equal("artifact_missing_file")
```

</details>

#### can append symbol and stale lookups to session evidence

- Verify: can append symbol and stale lookups to session evidence
   - Expected: with_symbol.evidence.len() equals `8)  # oracle: pinned constant asserted by this scenario`
   - Expected: with_symbol.evidence[7].action equals `symbol`
   - Expected: with_symbol.evidence[7].status equals `ok`
   - Expected: with_symbol.evidence[7].reason equals `render_tui_tree@1`
   - Expected: with_stale.evidence[9].action equals `symbol`
   - Expected: with_stale.evidence[9].status equals `stale`
   - Expected: with_stale.evidence[9].reason equals `unloaded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: can append symbol and stale lookups to session evidence")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val manifest = eager_default_manifest()
val loaded = dynsmf_session_autoload(dynsmf_session_new("test", dynsmf_policy_default()), manifest)
val with_symbol = dynsmf_session_record_symbol(loaded, "tui_renderer", "render_tui_tree")
expect(with_symbol.evidence.len()).to_equal(8)  # oracle: pinned constant asserted by this scenario
expect(with_symbol.evidence[7].action).to_equal("symbol")
expect(with_symbol.evidence[7].status).to_equal("ok")
expect(with_symbol.evidence[7].reason).to_equal("render_tui_tree@1")
val unloaded = dynsmf_session_unload(with_symbol, "tui_renderer")
val with_stale = dynsmf_session_record_symbol(unloaded, "tui_renderer", "render_tui_tree")
expect(with_stale.evidence[9].action).to_equal("symbol")
expect(with_stale.evidence[9].status).to_equal("stale")
expect(with_stale.evidence[9].reason).to_equal("unloaded")
```

</details>

#### unloads, reports stale symbol lookup, and reloads with fresh generation

- Verify: unloads, reports stale symbol lookup, and reloads with fresh generation
   - Expected: symbol_before.status equals `ok`
   - Expected: symbol_before.reason equals `render_tui_tree@1`
   - Expected: missing_symbol.status equals `missing`
   - Expected: unloaded.evidence[7].reason equals `smf_dlclose`
   - Expected: stale.status equals `stale`
   - Expected: symbol_after.status equals `ok`
   - Expected: reloaded.evidence[8].action equals `reload`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: unloads, reports stale symbol lookup, and reloads with fresh generation")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val manifest = eager_default_manifest()
val loaded = dynsmf_session_autoload(dynsmf_session_new("test", dynsmf_policy_default()), manifest)
val symbol_before = dynsmf_session_symbol(loaded, "tui_renderer", "render_tui_tree")
expect(symbol_before.status).to_equal("ok")
expect(symbol_before.reason).to_equal("render_tui_tree@1")
val missing_symbol = dynsmf_session_symbol(loaded, "tui_renderer", "missing_symbol")
expect(missing_symbol.status).to_equal("missing")
val unloaded = dynsmf_session_unload(loaded, "tui_renderer")
expect(unloaded.evidence[7].reason).to_equal("smf_dlclose")
val stale = dynsmf_session_symbol(unloaded, "tui_renderer", "render_tui_tree")
expect(stale.status).to_equal("stale")
val reloaded = dynsmf_session_autoload(unloaded, manifest)
val symbol_after = dynsmf_session_symbol(reloaded, "tui_renderer", "render_tui_tree")
expect(symbol_after.status).to_equal("ok")
expect(symbol_after.generation).to_be_greater_than(symbol_before.generation)
expect(reloaded.evidence[8].action).to_equal("reload")
```

</details>

### dynSMF interface fingerprint (heuristic exported-line hash input)

#### extracts only exported-signature lines and drops private helpers

- Verify: extracts only exported-signature lines and drops private helpers


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: extracts only exported-signature lines and drops private helpers")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val source_text = "fn helper() -> i64:\n    1\n\npub fn demo() -> i64:\n    2\n\nexport demo\n"
val fingerprint = dynsmf_interface_fingerprint(source_text)
expect(fingerprint).to_contain("pub fn demo() -> i64:")
expect(fingerprint).to_contain("export demo")
expect(fingerprint).to_not_contain("fn helper")
```

</details>

#### produces an unchanged fingerprint when only a private helper body changes

- Verify: produces an unchanged fingerprint when only a private helper body changes
   - Expected: dynsmf_interface_fingerprint(before) equals `dynsmf_interface_fingerprint(after)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: produces an unchanged fingerprint when only a private helper body changes")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val before = "pub fn demo() -> i64:\n    1\n\nfn helper() -> i64:\n    1\n"
val after = "pub fn demo() -> i64:\n    1\n\nfn helper() -> i64:\n    2\n"
expect(dynsmf_interface_fingerprint(before)).to_equal(dynsmf_interface_fingerprint(after))
```

</details>

#### produces a changed fingerprint when an exported signature changes

- Verify: produces a changed fingerprint when an exported signature changes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: produces a changed fingerprint when an exported signature changes")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val before = "pub fn demo() -> i64:\n    1\n"
val after = "pub fn demo(extra: i64) -> i64:\n    1\n"
expect(dynsmf_interface_fingerprint(before)).to_not_equal(dynsmf_interface_fingerprint(after))
```

</details>

### dynSMF abi_version + interface-hash hardening (fail-closed sidecars)

#### flags a missing abi sidecar as abi_mismatch (deliberate-red: fail-closed, never mask)

- Verify: flags a missing abi sidecar as abi_mismatch (deliberate-red: fail-closed, never mask)
   - Expected: status.ready is false
   - Expected: status.reason equals `abi_mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: flags a missing abi sidecar as abi_mismatch (deliberate-red: fail-closed, never mask)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val artifact_path = "build/dynsmf/_ifacehardening_spec_missing_abi.smf"
val source_path = "build/dynsmf/_ifacehardening_spec_missing_abi_src.spl"
file_write(source_path, "pub fn demo() -> i64:\n    1\n")
file_write(dynsmf_srchash_path(artifact_path), dynsmf_source_hash_current(source_path).to_text())
file_write(dynsmf_ifacehash_path(artifact_path), dynsmf_interface_hash_current(source_path).to_text())
# Deliberately do NOT write an `.abi` sidecar.
val entry = DynSmfManifestEntry(id: "spec_missing_abi", path: artifact_path, source_module: "test.mod", artifact_kind: "precompiled_smf", abi_version: "1", default_autoload: false, exports: [])
val status = dynsmf_artifact_status_with_hash(entry, true, spec_stub_honesty_padded_bytes(), source_path)
expect(status.ready).to_equal(false)
expect(status.reason).to_equal("abi_mismatch")
file_delete(source_path)
file_delete(dynsmf_srchash_path(artifact_path))
file_delete(dynsmf_ifacehash_path(artifact_path))
```

</details>

#### flags a wrong abi sidecar as abi_mismatch and never treats the artifact as loadable (deliberate-red)

- Verify: flags a wrong abi sidecar as abi_mismatch and never treats the artifact as loadable (deliberate-red)
   - Expected: status.ready is false
   - Expected: status.reason equals `abi_mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: flags a wrong abi sidecar as abi_mismatch and never treats the artifact as loadable (deliberate-red)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val artifact_path = "build/dynsmf/_ifacehardening_spec_wrong_abi.smf"
val source_path = "build/dynsmf/_ifacehardening_spec_wrong_abi_src.spl"
file_write(source_path, "pub fn demo() -> i64:\n    1\n")
file_write(dynsmf_srchash_path(artifact_path), dynsmf_source_hash_current(source_path).to_text())
file_write(dynsmf_ifacehash_path(artifact_path), dynsmf_interface_hash_current(source_path).to_text())
file_write(dynsmf_abi_path(artifact_path), "999")
val entry = DynSmfManifestEntry(id: "spec_wrong_abi", path: artifact_path, source_module: "test.mod", artifact_kind: "precompiled_smf", abi_version: "1", default_autoload: false, exports: [])
val status = dynsmf_artifact_status_with_hash(entry, true, spec_stub_honesty_padded_bytes(), source_path)
expect(status.ready).to_equal(false)
expect(status.reason).to_equal("abi_mismatch")
file_delete(source_path)
file_delete(dynsmf_srchash_path(artifact_path))
file_delete(dynsmf_ifacehash_path(artifact_path))
file_delete(dynsmf_abi_path(artifact_path))
```

</details>

#### reports the artifact ready when abi and srchash sidecars both match current source

- Verify: reports the artifact ready when abi and srchash sidecars both match current source
   - Expected: status.ready is true
   - Expected: status.reason equals `smf_artifact_ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: reports the artifact ready when abi and srchash sidecars both match current source")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val artifact_path = "build/dynsmf/_ifacehardening_spec_fresh.smf"
val source_path = "build/dynsmf/_ifacehardening_spec_fresh_src.spl"
file_write(source_path, "pub fn demo() -> i64:\n    1\n")
file_write(dynsmf_abi_path(artifact_path), "1")
file_write(dynsmf_srchash_path(artifact_path), dynsmf_source_hash_current(source_path).to_text())
val entry = DynSmfManifestEntry(id: "spec_fresh", path: artifact_path, source_module: "test.mod", artifact_kind: "precompiled_smf", abi_version: "1", default_autoload: false, exports: [])
val status = dynsmf_artifact_status_with_hash(entry, true, spec_stub_honesty_padded_bytes(), source_path)
expect(status.ready).to_equal(true)
expect(status.reason).to_equal("smf_artifact_ready")
file_delete(source_path)
file_delete(dynsmf_abi_path(artifact_path))
file_delete(dynsmf_srchash_path(artifact_path))
```

</details>

#### reports stale_impl when srchash is stale but the interface hash is unchanged (module-only rebuild)

- Verify: reports stale_impl when srchash is stale but the interface hash is unchanged (module-only rebuild)
   - Expected: status.ready is false
   - Expected: status.reason equals `stale_impl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: reports stale_impl when srchash is stale but the interface hash is unchanged (module-only rebuild)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val artifact_path = "build/dynsmf/_ifacehardening_spec_stale_impl.smf"
val source_path = "build/dynsmf/_ifacehardening_spec_stale_impl_src.spl"
file_write(source_path, "pub fn demo() -> i64:\n    1\n")
file_write(dynsmf_abi_path(artifact_path), "1")
# srchash sidecar deliberately stale (does not match current whole-file hash).
file_write(dynsmf_srchash_path(artifact_path), "1")
# ifacehash sidecar matches the CURRENT exported-interface fingerprint (signature unchanged).
file_write(dynsmf_ifacehash_path(artifact_path), dynsmf_interface_hash_current(source_path).to_text())
val entry = DynSmfManifestEntry(id: "spec_stale_impl", path: artifact_path, source_module: "test.mod", artifact_kind: "precompiled_smf", abi_version: "1", default_autoload: false, exports: [])
val status = dynsmf_artifact_status_with_hash(entry, true, spec_stub_honesty_padded_bytes(), source_path)
expect(status.ready).to_equal(false)
expect(status.reason).to_equal("stale_impl")
file_delete(source_path)
file_delete(dynsmf_abi_path(artifact_path))
file_delete(dynsmf_srchash_path(artifact_path))
file_delete(dynsmf_ifacehash_path(artifact_path))
```

</details>

#### reports stale_interface when both srchash and the interface hash are stale (dependents need a rebuild)

- Verify: reports stale_interface when both srchash and the interface hash are stale (dependents need a rebuild)
   - Expected: status.ready is false
   - Expected: status.reason equals `stale_interface`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: reports stale_interface when both srchash and the interface hash are stale (dependents need a rebuild)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val artifact_path = "build/dynsmf/_ifacehardening_spec_stale_interface.smf"
val source_path = "build/dynsmf/_ifacehardening_spec_stale_interface_src.spl"
file_write(source_path, "pub fn demo() -> i64:\n    1\n")
file_write(dynsmf_abi_path(artifact_path), "1")
file_write(dynsmf_srchash_path(artifact_path), "1")
file_write(dynsmf_ifacehash_path(artifact_path), "1")
val entry = DynSmfManifestEntry(id: "spec_stale_interface", path: artifact_path, source_module: "test.mod", artifact_kind: "precompiled_smf", abi_version: "1", default_autoload: false, exports: [])
val status = dynsmf_artifact_status_with_hash(entry, true, spec_stub_honesty_padded_bytes(), source_path)
expect(status.ready).to_equal(false)
expect(status.reason).to_equal("stale_interface")
file_delete(source_path)
file_delete(dynsmf_abi_path(artifact_path))
file_delete(dynsmf_srchash_path(artifact_path))
file_delete(dynsmf_ifacehash_path(artifact_path))
```

</details>

#### falls back to stale_source when the ifacehash sidecar is absent (legacy artifact, cannot distinguish)

- Verify: falls back to stale_source when the ifacehash sidecar is absent (legacy artifact, cannot distinguish)
   - Expected: status.ready is false
   - Expected: status.reason equals `stale_source`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: falls back to stale_source when the ifacehash sidecar is absent (legacy artifact, cannot distinguish)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val artifact_path = "build/dynsmf/_ifacehardening_spec_missing_ifacehash.smf"
val source_path = "build/dynsmf/_ifacehardening_spec_missing_ifacehash_src.spl"
file_write(source_path, "pub fn demo() -> i64:\n    1\n")
file_write(dynsmf_abi_path(artifact_path), "1")
file_write(dynsmf_srchash_path(artifact_path), "1")
# Deliberately no `.ifacehash` sidecar written.
val entry = DynSmfManifestEntry(id: "spec_missing_ifacehash", path: artifact_path, source_module: "test.mod", artifact_kind: "precompiled_smf", abi_version: "1", default_autoload: false, exports: [])
val status = dynsmf_artifact_status_with_hash(entry, true, spec_stub_honesty_padded_bytes(), source_path)
expect(status.ready).to_equal(false)
expect(status.reason).to_equal("stale_source")
file_delete(source_path)
file_delete(dynsmf_abi_path(artifact_path))
file_delete(dynsmf_srchash_path(artifact_path))
```

</details>

### dynSMF toolchain entries — fresh-sidecar status transitions (on-demand, default_autoload:false)

#### reports each new toolchain entry ready when abi and srchash sidecars match current source

- Verify: reports each new toolchain entry ready when abi and srchash sidecars match current source
   - Expected: status.ready is true
   - Expected: status.reason equals `smf_artifact_ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: reports each new toolchain entry ready when abi and srchash sidecars match current source")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val manifest = eager_default_manifest()
val plans = dynsmf_build_plans(manifest)
var idx = 7
while idx < 12:
    val entry = manifest[idx]
    val source_path = plans[idx].source_path
    file_write(dynsmf_abi_path(entry.path), entry.abi_version)
    file_write(dynsmf_srchash_path(entry.path), dynsmf_source_hash_current(source_path).to_text())
    val data = if entry.exports.len() == 0: spec_stub_honesty_padded_bytes() else: spec_stub_honesty_witness_bytes(entry.exports)
    val status = dynsmf_artifact_status_with_hash(entry, true, data, source_path)
    expect(status.ready).to_equal(true)
    expect(status.reason).to_equal("smf_artifact_ready")
    file_delete(dynsmf_abi_path(entry.path))
    file_delete(dynsmf_srchash_path(entry.path))
    idx = idx + 1
```

</details>

#### flags a missing abi sidecar as abi_mismatch for a new toolchain entry too (fail-closed applies uniformly)

- Verify: flags a missing abi sidecar as abi_mismatch for a new toolchain entry too (fail-closed applies uniformly)
   - Expected: entry.id equals `todo_scan`
   - Expected: status.ready is false
   - Expected: status.reason equals `abi_mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: flags a missing abi sidecar as abi_mismatch for a new toolchain entry too (fail-closed applies uniformly)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val manifest = eager_default_manifest()
val plans = dynsmf_build_plans(manifest)
val entry = manifest[11]
val source_path = plans[11].source_path
expect(entry.id).to_equal("todo_scan")
file_write(dynsmf_srchash_path(entry.path), dynsmf_source_hash_current(source_path).to_text())
# Deliberately do NOT write an `.abi` sidecar.
val status = dynsmf_artifact_status_with_hash(entry, true, spec_stub_honesty_witness_bytes(entry.exports), source_path)
expect(status.ready).to_equal(false)
expect(status.reason).to_equal("abi_mismatch")
file_delete(dynsmf_srchash_path(entry.path))
```

</details>

### dynSMF stub-artifact honesty (export-witness check, doc/08_tracking/bug/seed_compile_smf_stub_fail_open_2026-07-17.md)

#### reports stub_artifact for a stub-sized (219-byte) artifact with NO witnessed exports, even with fresh abi/srchash/ifacehash sidecars (deliberate-red: byte-for-byte length of today's real hollow stub)

- Verify: reports stub_artifact for a stub-sized (219-byte) artifact with NO witnessed exports, even with fresh abi/srchash/ifaceh
   - Expected: data.len() equals `219)  # oracle: pinned constant asserted by this scenario`
   - Expected: status.ready is false
   - Expected: status.reason equals `stub_artifact`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: reports stub_artifact for a stub-sized (219-byte) artifact with NO witnessed exports, even with fresh abi/srchash/ifaceh")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val artifact_path = "build/dynsmf/_stubhonesty_spec_stub_sized.smf"
val source_path = "build/dynsmf/_stubhonesty_spec_stub_sized_src.spl"
file_write(source_path, "pub fn demo() -> i64:\n    1\n")
file_write(dynsmf_abi_path(artifact_path), "1")
file_write(dynsmf_srchash_path(artifact_path), dynsmf_source_hash_current(source_path).to_text())
file_write(dynsmf_ifacehash_path(artifact_path), dynsmf_interface_hash_current(source_path).to_text())
val entry = DynSmfManifestEntry(id: "spec_stub_sized", path: artifact_path, source_module: "test.mod", artifact_kind: "precompiled_smf", abi_version: "1", default_autoload: false, exports: ["open", "close"])
# Hand-written literal bytes: magic + zero padding to exactly 219
# bytes (the known real stub size) — no "open"/"close" names present,
# matching the actual build/dynsmf/*.smf stubs on disk today.
val data = [83, 77, 70, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0]
expect(data.len()).to_equal(219)  # oracle: pinned constant asserted by this scenario
val status = dynsmf_artifact_status_with_hash(entry, true, data, source_path)
expect(status.ready).to_equal(false)
expect(status.reason).to_equal("stub_artifact")
file_delete(source_path)
file_delete(dynsmf_abi_path(artifact_path))
file_delete(dynsmf_srchash_path(artifact_path))
file_delete(dynsmf_ifacehash_path(artifact_path))
```

</details>

#### reports stub_artifact when the payload exceeds the stub size but lacks the required export names (padding alone does not satisfy the witness)

- Verify: reports stub_artifact when the payload exceeds the stub size but lacks the required export names (padding alone does not
   - Expected: status.ready is false
   - Expected: status.reason equals `stub_artifact`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: reports stub_artifact when the payload exceeds the stub size but lacks the required export names (padding alone does not")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val artifact_path = "build/dynsmf/_stubhonesty_spec_padding_only.smf"
val entry = DynSmfManifestEntry(id: "spec_padding_only", path: artifact_path, source_module: "test.mod", artifact_kind: "precompiled_smf", abi_version: "1", default_autoload: false, exports: ["open", "close"])
val status = dynsmf_artifact_status_with_hash(entry, true, spec_stub_honesty_padded_bytes(), "")
expect(status.ready).to_equal(false)
expect(status.reason).to_equal("stub_artifact")
```

</details>

#### passes the export-witness check when the payload exceeds the stub size AND the artifact's own bytes carry the required export names

- Verify: passes the export-witness check when the payload exceeds the stub size AND the artifact's own bytes carry the required e
   - Expected: data.len() equals `235)  # oracle: pinned constant asserted by this scenario`
   - Expected: status.ready is true
   - Expected: status.reason equals `smf_artifact_ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: passes the export-witness check when the payload exceeds the stub size AND the artifact's own bytes carry the required e")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val artifact_path = "build/dynsmf/_stubhonesty_spec_with_witness.smf"
val source_path = "build/dynsmf/_stubhonesty_spec_with_witness_src.spl"
file_write(source_path, "pub fn demo() -> i64:\n    1\n")
file_write(dynsmf_abi_path(artifact_path), "1")
file_write(dynsmf_srchash_path(artifact_path), dynsmf_source_hash_current(source_path).to_text())
val entry = DynSmfManifestEntry(id: "spec_with_witness", path: artifact_path, source_module: "test.mod", artifact_kind: "precompiled_smf", abi_version: "1", default_autoload: false, exports: ["open", "close"])
# Hand-written literal bytes, constructed independently of the
# checker's own parsing code (smf_artifact_has_export in
# src/os/smf/smf_dynlib.spl) — NOT produced via
# spec_stub_honesty_witness_bytes. magic(4) + 220 zero-padding bytes
# (> the 219-byte stub floor) + "open\0" + "close\0" (null-terminated
# ASCII, the real SMF string-table convention):
val data = [83, 77, 70, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    111, 112, 101, 110, 0, 99, 108, 111, 115, 101, 0]
expect(data.len()).to_equal(235)  # oracle: pinned constant asserted by this scenario
val status = dynsmf_artifact_status_with_hash(entry, true, data, source_path)
expect(status.ready).to_equal(true)
expect(status.reason).to_equal("smf_artifact_ready")
file_delete(source_path)
file_delete(dynsmf_abi_path(artifact_path))
file_delete(dynsmf_srchash_path(artifact_path))
```

</details>

#### reports stub_artifact for an empty-exports entry whose payload does not exceed the known stub size (honesty floor)

- Verify: reports stub_artifact for an empty-exports entry whose payload does not exceed the known stub size (honesty floor)
   - Expected: status.ready is false
   - Expected: status.reason equals `stub_artifact`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: reports stub_artifact for an empty-exports entry whose payload does not exceed the known stub size (honesty floor)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val artifact_path = "build/dynsmf/_stubhonesty_spec_empty_exports_small.smf"
val entry = DynSmfManifestEntry(id: "spec_empty_exports_small", path: artifact_path, source_module: "test.mod", artifact_kind: "precompiled_smf", abi_version: "1", default_autoload: false, exports: [])
val status = dynsmf_artifact_status_with_hash(entry, true, [83, 77, 70, 0], "")
expect(status.ready).to_equal(false)
expect(status.reason).to_equal("stub_artifact")
```

</details>

#### passes the honesty floor for an empty-exports entry whose payload exceeds the known 219-byte stub size

- Verify: passes the honesty floor for an empty-exports entry whose payload exceeds the known 219-byte stub size
   - Expected: status.ready is true
   - Expected: status.reason equals `smf_artifact_ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-004 REQ-005 REQ-006 REQ-007 REQ-008 REQ-009 REQ-010
step("Verify: passes the honesty floor for an empty-exports entry whose payload exceeds the known 219-byte stub size")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val artifact_path = "build/dynsmf/_stubhonesty_spec_empty_exports_large.smf"
val source_path = "build/dynsmf/_stubhonesty_spec_empty_exports_large_src.spl"
file_write(source_path, "pub fn demo() -> i64:\n    1\n")
file_write(dynsmf_abi_path(artifact_path), "1")
file_write(dynsmf_srchash_path(artifact_path), dynsmf_source_hash_current(source_path).to_text())
val entry = DynSmfManifestEntry(id: "spec_empty_exports_large", path: artifact_path, source_module: "test.mod", artifact_kind: "precompiled_smf", abi_version: "1", default_autoload: false, exports: [])
val status = dynsmf_artifact_status_with_hash(entry, true, spec_stub_honesty_padded_bytes(), source_path)
expect(status.ready).to_equal(true)
expect(status.reason).to_equal("smf_artifact_ready")
file_delete(source_path)
file_delete(dynsmf_abi_path(artifact_path))
file_delete(dynsmf_srchash_path(artifact_path))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 36 |
| Active scenarios | 36 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/nfr/low_dependency_ui_dynsmf.md`
- **Plan:** `doc/03_plan/sys_test/low_dependency_ui_dynsmf_dynsmf_session.md`
- **Design:** `doc/05_design/low_dependency_ui_dynsmf.md`
- **Research:** `doc/01_research/local/low_dependency_ui_dynsmf.md`


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `821836b34048009cb5f8d3d51e0e7435d3f04dc0a008cf78a3d8219750e4c276`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `821836b34048009cb5f8d3d51e0e7435d3f04dc0a008cf78a3d8219750e4c276`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `821836b34048009cb5f8d3d51e0e7435d3f04dc0a008cf78a3d8219750e4c276`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/smf/dynsmf_session_spec.spl
mirror: doc/06_spec/01_unit/os/smf/dynsmf_session_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/smf/dynsmf_session_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/smf/dynsmf_session_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/smf/dynsmf_session_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/smf/dynsmf_session_spec.spl:425:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can append symbol and stale lookups to session evidence' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
