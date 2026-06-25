# dynSMF Startup Autoload Policy Integration Specification

> Verifies that app startup can construct a dynSMF session from command-line arguments and environment values, autoload the six selected stdlib-like precompiled SMF libraries by default, and honor the root entrypoint's `--dynsmf-status`, `--no-dynsmf`, and `--disable-dynsmf=<ids>` controls.

<!-- sdn-diagram:id=dynsmf_autoload_policy_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dynsmf_autoload_policy_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dynsmf_autoload_policy_spec -> std
dynsmf_autoload_policy_spec -> os
dynsmf_autoload_policy_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dynsmf_autoload_policy_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# dynSMF Startup Autoload Policy Integration Specification

Verifies that app startup can construct a dynSMF session from command-line arguments and environment values, autoload the six selected stdlib-like precompiled SMF libraries by default, and honor the root entrypoint's `--dynsmf-status`, `--no-dynsmf`, and `--disable-dynsmf=<ids>` controls.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/nfr/low_dependency_ui_dynsmf.md |
| Plan | doc/03_plan/sys_test/low_dependency_ui_dynsmf_dynsmf_session.md |
| Design | doc/05_design/low_dependency_ui_dynsmf.md |
| Research | doc/01_research/local/low_dependency_ui_dynsmf.md |
| Source | `test/02_integration/app/simple/dynsmf_autoload_policy_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that app startup can construct a dynSMF session from command-line
arguments and environment values, autoload the six selected stdlib-like
precompiled SMF libraries by default, and honor the root entrypoint's
`--dynsmf-status`, `--no-dynsmf`, and `--disable-dynsmf=<ids>` controls.

## Examples

Plain startup policy loads the six default manifest entries. `--no-dynsmf`
suppresses every default autoload. A per-id disable policy skips only the named
library while leaving the other stdlib-like dynSMF libraries loaded. The app
root status command prints deterministic evidence rows without changing the
quiet plain invocation behavior. Startup uses checked autoload, so enabled
entries must have ready `build/dynsmf/*.smf` artifacts before `smf_dlopen`.
The spec invokes `scripts/check/check-low-dependency-dynsmf-build-plans.shs`
when those artifacts are absent so a fresh workspace can produce the same
startup evidence.

**Requirements:** doc/02_requirements/feature/low_dependency_ui_dynsmf.md
**Requirements:** doc/02_requirements/nfr/low_dependency_ui_dynsmf.md
**Traceability:** REQ-005, REQ-006, REQ-007, REQ-009, REQ-010, NFR-003, NFR-004, NFR-006
**Plan:** doc/03_plan/sys_test/low_dependency_ui_dynsmf_dynsmf_session.md
**Design:** doc/05_design/low_dependency_ui_dynsmf.md
**Research:** doc/01_research/local/low_dependency_ui_dynsmf.md

## Scenarios

### dynSMF startup autoload policy

#### queues background compile evidence before checked autoload for missing artifacts

1. DynSmfManifestEntry

2. DynSmfManifestEntry
   - Expected: session.loaded.len() equals `0`
   - Expected: session.evidence.len() equals `4`
   - Expected: session.evidence[0].library_id equals `file_io`
   - Expected: session.evidence[0].action equals `compile_background`
   - Expected: session.evidence[0].status equals `queued`
   - Expected: session.evidence[1].library_id equals `gui_renderer`
   - Expected: session.evidence[1].action equals `compile_background`
   - Expected: session.evidence[1].status equals `queued`
   - Expected: session.evidence[2].status equals `failed`
   - Expected: session.evidence[2].reason equals `artifact_missing_file`


<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = [
    DynSmfManifestEntry(id: "file_io", path: "build/dynsmf/startup_missing_file_io.smf", source_module: "std.io", artifact_kind: "precompiled_smf", abi_version: "1", default_autoload: true, exports: ["open"]),
    DynSmfManifestEntry(id: "gui_renderer", path: "build/dynsmf/startup_missing_gui_renderer.smf", source_module: "app.ui.web.backend", artifact_kind: "precompiled_smf", abi_version: "1", default_autoload: true, exports: ["render_gui"])
]
val session = dynsmf_startup_session_for_manifest_from_values([], "", "", "integration-background", manifest)
expect(session.loaded.len()).to_equal(0)
expect(session.evidence.len()).to_equal(4)
expect(session.evidence[0].library_id).to_equal("file_io")
expect(session.evidence[0].action).to_equal("compile_background")
expect(session.evidence[0].status).to_equal("queued")
expect(session.evidence[0].reason).to_contain("bin/simple compile src/lib/nogc_sync_mut/io/file.spl")
expect(session.evidence[1].library_id).to_equal("gui_renderer")
expect(session.evidence[1].action).to_equal("compile_background")
expect(session.evidence[1].status).to_equal("queued")
expect(session.evidence[1].reason).to_contain("src/app/ui.web/backend.spl")
expect(session.evidence[2].status).to_equal("failed")
expect(session.evidence[2].reason).to_equal("artifact_missing_file")
```

</details>

#### autoloads all six default stdlib-like dynSMF entries for startup

1. var session = dynsmf startup session from values
   - Expected: build.2 equals `0`

2. session = dynsmf startup session from values
   - Expected: session.loaded.len() equals `6`
   - Expected: session.evidence.len() equals `6`
   - Expected: session.evidence[0].library_id equals `file_io`
   - Expected: session.evidence[5].library_id equals `tui_renderer`
   - Expected: session.evidence[5].reason equals `smf_dlopen`


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = dynsmf_startup_session_from_values([], "", "", "integration-default")
if session.loaded.len() != 6:
    val build = ensure_low_dependency_dynsmf_artifacts()
    expect(build.2).to_equal(0)
    session = dynsmf_startup_session_from_values([], "", "", "integration-default")
expect(session.loaded.len()).to_equal(6)
expect(session.evidence.len()).to_equal(6)
expect(session.evidence[0].library_id).to_equal("file_io")
expect(session.evidence[5].library_id).to_equal("tui_renderer")
expect(session.evidence[5].reason).to_equal("smf_dlopen")
```

</details>

#### honors skip-all startup policy from args and env values

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val by_arg = dynsmf_startup_session_from_values(["--no-dynsmf"], "", "", "integration-no-arg")
expect(by_arg.loaded.len()).to_equal(0)
expect(by_arg.evidence.len()).to_equal(6)
expect(by_arg.evidence[0].action).to_equal("skip")
expect(by_arg.evidence[0].policy_source).to_equal("arg:--no-dynsmf")

val by_env = dynsmf_startup_session_from_values([], "0", "", "integration-no-env")
expect(by_env.loaded.len()).to_equal(0)
expect(by_env.evidence[5].action).to_equal("skip")
expect(by_env.evidence[5].policy_source).to_equal("env:SIMPLE_DYNSMF")
```

</details>

#### honors per-id startup disable policy while loading other libraries

1. var session = dynsmf startup session from values
   - Expected: build.2 equals `0`

2. session = dynsmf startup session from values
   - Expected: session.loaded.len() equals `4`
   - Expected: session.evidence[3].library_id equals `web_renderer`
   - Expected: session.evidence[3].action equals `skip`
   - Expected: session.evidence[5].library_id equals `tui_renderer`
   - Expected: session.evidence[5].action equals `skip`


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = dynsmf_startup_session_from_values(["--disable-dynsmf=web_renderer,tui_renderer"], "", "", "integration-disable")
if session.loaded.len() != 4:
    val build = ensure_low_dependency_dynsmf_artifacts()
    expect(build.2).to_equal(0)
    session = dynsmf_startup_session_from_values(["--disable-dynsmf=web_renderer,tui_renderer"], "", "", "integration-disable")
expect(session.loaded.len()).to_equal(4)
expect(session.evidence[3].library_id).to_equal("web_renderer")
expect(session.evidence[3].action).to_equal("skip")
expect(session.evidence[5].library_id).to_equal("tui_renderer")
expect(session.evidence[5].action).to_equal("skip")
```

</details>

#### exposes app root dynSMF status evidence without noisy plain startup

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val build = ensure_low_dependency_dynsmf_artifacts()
expect(build.2).to_equal(0)

val (plain_out, plain_err, plain_code) = run_app_root_dynsmf([])
expect(plain_code).to_equal(0)
expect(plain_out).to_equal("")

val (out, err, code) = run_app_root_dynsmf(["--dynsmf-status"])
expect(code).to_equal(0)
expect(out).to_contain("dynsmf session=app-root")
expect(out).to_contain("loaded=6")
expect(out).to_contain("tui_renderer:load:default:loaded:smf_dlopen")
```

</details>

#### exposes app root dynSMF opt-out evidence

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (out, err, code) = run_app_root_dynsmf(["--no-dynsmf", "--dynsmf-status"])
expect(code).to_equal(0)
expect(out).to_contain("policy=arg:--no-dynsmf")
expect(out).to_contain("loaded=0")
expect(out).to_contain("skipped=6")
expect(out).to_contain("file_io:skip:arg:--no-dynsmf:skipped:disabled")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/nfr/low_dependency_ui_dynsmf.md](doc/02_requirements/nfr/low_dependency_ui_dynsmf.md)
- **Plan:** [doc/03_plan/sys_test/low_dependency_ui_dynsmf_dynsmf_session.md](doc/03_plan/sys_test/low_dependency_ui_dynsmf_dynsmf_session.md)
- **Design:** [doc/05_design/low_dependency_ui_dynsmf.md](doc/05_design/low_dependency_ui_dynsmf.md)
- **Research:** [doc/01_research/local/low_dependency_ui_dynsmf.md](doc/01_research/local/low_dependency_ui_dynsmf.md)


</details>
