# dynSMF Session Specification

> Verifies selected low_dependency_ui_dynsmf session behavior for the requested stdlib-like dynSMF libraries. The spec covers manifest declaration, build-plan generation, artifact-readiness validation, argument/environment policy parsing, session-scoped autoload evidence, unload, stale symbol lookup, and reload generation changes.

<!-- sdn-diagram:id=dynsmf_session_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dynsmf_session_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dynsmf_session_spec -> std
dynsmf_session_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dynsmf_session_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# dynSMF Session Specification

Verifies selected low_dependency_ui_dynsmf session behavior for the requested stdlib-like dynSMF libraries. The spec covers manifest declaration, build-plan generation, artifact-readiness validation, argument/environment policy parsing, session-scoped autoload evidence, unload, stale symbol lookup, and reload generation changes.

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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies selected low_dependency_ui_dynsmf session behavior for the requested
stdlib-like dynSMF libraries. The spec covers manifest declaration, build-plan
generation, artifact-readiness validation, argument/environment policy parsing,
session-scoped autoload evidence, unload, stale symbol lookup, and reload
generation changes.

## Examples

The default manifest declares all requested stdlib-like dynSMF ids as
precompiled SMF artifacts and autoloads enabled entries by default. A disabled
policy records skip evidence, and an unloaded session reports stale symbol
evidence until the library is loaded again. Checked sessions use
`smf_dlopen_checked`, `smf_dlsym`, and `smf_dlclose` so the evidence proves the
dynSMF path instead of a separate fake loader. Checked load validates missing,
short, and invalid SMF artifacts before accepting a handle.

**Requirements:** doc/02_requirements/feature/low_dependency_ui_dynsmf.md
**Requirements:** doc/02_requirements/nfr/low_dependency_ui_dynsmf.md
**Traceability:** REQ-004, REQ-005, REQ-006, REQ-007, REQ-008, REQ-009, REQ-010, NFR-003, NFR-004, NFR-005, NFR-006
**Plan:** doc/03_plan/sys_test/low_dependency_ui_dynsmf_dynsmf_session.md
**Design:** doc/05_design/low_dependency_ui_dynsmf.md
**Research:** doc/01_research/local/low_dependency_ui_dynsmf.md

## Scenarios

### dynSMF manifest

#### declares all requested stdlib-like library ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = dynsmf_default_manifest()
expect(manifest[0].id).to_equal("file_io")
expect(manifest[1].id).to_equal("net_io")
expect(manifest[2].id).to_equal("render2d")
expect(manifest[3].id).to_equal("web_renderer")
expect(manifest[4].id).to_equal("gui_renderer")
expect(manifest[5].id).to_equal("tui_renderer")
expect(manifest[6].id).to_equal("ui_html")
expect(dynsmf_manifest_all_precompiled(manifest)).to_equal(true)
expect(manifest[0].artifact_kind).to_equal("precompiled_smf")
expect(manifest[0].default_autoload).to_equal(true)
expect(manifest[5].default_autoload).to_equal(true)
expect(manifest[6].default_autoload).to_equal(true)
```

</details>

#### creates deterministic compile plans for all precompiled artifacts

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = dynsmf_default_manifest()
val plans = dynsmf_build_plans(manifest)
expect(plans.len()).to_equal(7)
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

#### records general background compile evidence for non-gui and gui artifacts

- DynSmfManifestEntry
- DynSmfManifestEntry
- DynSmfManifestEntry
- DynSmfManifestEntry
- DynSmfManifestEntry
- DynSmfArtifactStatus
- DynSmfArtifactStatus
- DynSmfArtifactStatus
- DynSmfArtifactStatus
- DynSmfArtifactStatus
   - Expected: session.evidence.len() equals `5`
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

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
expect(session.evidence.len()).to_equal(5)
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = dynsmf_default_manifest()[0]
val ready = dynsmf_artifact_status_from_bytes(entry, true, [83, 77, 70, 0, 1, 2])
expect(ready.ready).to_equal(true)
expect(ready.reason).to_equal("smf_artifact_ready")
expect(ready.byte_count).to_equal(6)
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = dynsmf_policy_from_args_env(["--no-dynsmf"], "", "")
expect(policy.disabled_all).to_equal(true)
expect(policy.source).to_equal("arg:--no-dynsmf")
```

</details>

#### supports skip all from env

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = dynsmf_policy_from_args_env([], "0", "")
expect(policy.disabled_all).to_equal(true)
expect(policy.source).to_equal("env:SIMPLE_DYNSMF")
```

</details>

#### supports per-id disable from args

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = dynsmf_policy_from_args_env(["--disable-dynsmf=web_renderer,tui_renderer"], "", "")
expect(dynsmf_id_disabled(policy, "web_renderer")).to_equal(true)
expect(dynsmf_id_disabled(policy, "tui_renderer")).to_equal(true)
expect(dynsmf_id_disabled(policy, "net_io")).to_equal(false)
expect(policy.source).to_equal("arg:--disable-dynsmf")
```

</details>

#### supports per-id disable from env

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = dynsmf_policy_from_args_env([], "", "web_renderer,tui_renderer")
expect(dynsmf_id_disabled(policy, "web_renderer")).to_equal(true)
expect(dynsmf_id_disabled(policy, "tui_renderer")).to_equal(true)
expect(dynsmf_id_disabled(policy, "file_io")).to_equal(false)
expect(policy.source).to_equal("env:SIMPLE_DYNSMF_DISABLE")
```

</details>

### dynSMF session lifecycle

#### autoloads tui_renderer and records evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = dynsmf_default_manifest()
val session = dynsmf_session_autoload(dynsmf_session_new("test", dynsmf_policy_default()), manifest)
expect(session.loaded.len()).to_equal(7)
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = dynsmf_default_manifest()
val policy = dynsmf_policy_from_args_env(["--disable-dynsmf=tui_renderer"], "", "")
val session = dynsmf_session_autoload(dynsmf_session_new("test", policy), manifest)
expect(session.loaded.len()).to_equal(6)
expect(session.loaded[0].id).to_equal("file_io")
expect(session.evidence[5].library_id).to_equal("tui_renderer")
expect(session.evidence[5].action).to_equal("skip")
expect(session.evidence[5].reason).to_equal("disabled")
expect(session.evidence[6].library_id).to_equal("ui_html")
expect(session.evidence[6].action).to_equal("load")
```

</details>

#### records skip evidence for every default when all dynSMF loading is disabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = dynsmf_default_manifest()
val policy = dynsmf_policy_from_args_env(["--no-dynsmf"], "", "")
val session = dynsmf_session_autoload(dynsmf_session_new("test", policy), manifest)
expect(session.loaded.len()).to_equal(0)
expect(session.evidence.len()).to_equal(7)
expect(session.evidence[0].action).to_equal("skip")
expect(session.evidence[5].library_id).to_equal("tui_renderer")
expect(session.evidence[5].policy_source).to_equal("arg:--no-dynsmf")
expect(session.evidence[6].library_id).to_equal("ui_html")
expect(session.evidence[6].action).to_equal("skip")
```

</details>

#### checked loading fails before dlopen when the artifact file is missing

- DynSmfManifestEntry
   - Expected: session.loaded.len() equals `0`
   - Expected: session.evidence.len() equals `1`
   - Expected: session.evidence[0].status equals `failed`
   - Expected: session.evidence[0].reason equals `artifact_missing_file`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = [
    DynSmfManifestEntry(id: "missing", path: "build/dynsmf/does_not_exist_for_dynsmf_session_spec.smf", source_module: "std.missing", artifact_kind: "precompiled_smf", abi_version: "1", default_autoload: true, exports: ["open"])
]
val session = dynsmf_session_load_checked(dynsmf_session_new("checked", dynsmf_policy_default()), manifest, "missing")
expect(session.loaded.len()).to_equal(0)
expect(session.evidence.len()).to_equal(1)
expect(session.evidence[0].status).to_equal("failed")
expect(session.evidence[0].reason).to_equal("artifact_missing_file")
```

</details>

#### can append symbol and stale lookups to session evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = dynsmf_default_manifest()
val loaded = dynsmf_session_autoload(dynsmf_session_new("test", dynsmf_policy_default()), manifest)
val with_symbol = dynsmf_session_record_symbol(loaded, "tui_renderer", "render_tui_tree")
expect(with_symbol.evidence.len()).to_equal(8)
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = dynsmf_default_manifest()
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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/nfr/low_dependency_ui_dynsmf.md](doc/02_requirements/nfr/low_dependency_ui_dynsmf.md)
- **Plan:** [doc/03_plan/sys_test/low_dependency_ui_dynsmf_dynsmf_session.md](doc/03_plan/sys_test/low_dependency_ui_dynsmf_dynsmf_session.md)
- **Design:** [doc/05_design/low_dependency_ui_dynsmf.md](doc/05_design/low_dependency_ui_dynsmf.md)
- **Research:** [doc/01_research/local/low_dependency_ui_dynsmf.md](doc/01_research/local/low_dependency_ui_dynsmf.md)


</details>
