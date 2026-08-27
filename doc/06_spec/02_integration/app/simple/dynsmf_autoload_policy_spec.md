# dynSMF Startup Autoload Policy Integration Specification

> Verifies that app startup can construct a dynSMF session from command-line arguments and environment values, autoload the seven selected stdlib-like precompiled SMF libraries by default, and honor the root entrypoint's `--dynsmf-status`, `--no-dynsmf`, and `--disable-dynsmf=<ids>` controls.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# dynSMF Startup Autoload Policy Integration Specification

Verifies that app startup can construct a dynSMF session from command-line arguments and environment values, autoload the seven selected stdlib-like precompiled SMF libraries by default, and honor the root entrypoint's `--dynsmf-status`, `--no-dynsmf`, and `--disable-dynsmf=<ids>` controls.

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that app startup can construct a dynSMF session from command-line
arguments and environment values, autoload the seven selected stdlib-like
precompiled SMF libraries by default, and honor the root entrypoint's
`--dynsmf-status`, `--no-dynsmf`, and `--disable-dynsmf=<ids>` controls.

## Examples

Plain startup policy loads the seven default manifest entries. `--no-dynsmf`
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- queues background compile evidence before checked autoload for missing artifacts
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

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("queues background compile evidence before checked autoload for missing artifacts")
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

- demand-load policy: default startup loads nothing and queues nothing
   - Expected: session.loaded.len() equals `0`
   - Expected: session.evidence.len() equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("demand-load policy: default startup loads nothing and queues nothing")
# Perf program 2026-08-10: the seven stdlib-like entries are
# demand-loaded, so a plain startup session performs zero loads,
# zero background-compile queueing, and zero spawns.
val session = dynsmf_startup_session_from_values([], "", "", "integration-default")
expect(session.loaded.len()).to_equal(0)
expect(session.evidence.len()).to_equal(0)
```

</details>

#### skip-all startup policy still yields an empty demand-load startup session

- skip-all startup policy still yields an empty demand-load startup session
   - Expected: by_arg.loaded.len() equals `0`
   - Expected: by_arg.policy.source equals `arg:--no-dynsmf`
   - Expected: by_arg.evidence.len() equals `0`
   - Expected: by_env.loaded.len() equals `0`
   - Expected: by_env.policy.source equals `env:SIMPLE_DYNSMF`
   - Expected: by_env.evidence.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
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


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("honors per-id disable policy on an explicit autoload manifest")
val manifest = [
    DynSmfManifestEntry(id: "tui_renderer", path: "build/dynsmf/policy_tui_renderer.smf", source_module: "app.ui.render.tui_widgets", artifact_kind: "precompiled_smf", abi_version: "1", default_autoload: true, exports: ["render_tui_tree"])
]
val session = dynsmf_startup_session_for_manifest_from_values(["--disable-dynsmf=tui_renderer"], "", "", "integration-disable", manifest)
expect(session.loaded.len()).to_equal(0)
var saw_skip = false
for row in session.evidence:
    if row.library_id == "tui_renderer" and row.action == "skip":
        saw_skip = true
expect(saw_skip).to_equal(true)
```

</details>

#### exposes app root dynSMF status evidence without noisy plain startup

- exposes app root dynSMF status evidence without noisy plain startup
   - Expected: plain_code equals `0`
   - Expected: plain_out equals ``
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("exposes app root dynSMF status evidence without noisy plain startup")
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

- exposes app root dynSMF opt-out evidence
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("exposes app root dynSMF opt-out evidence")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-005`
- `REQ-006`
- `REQ-007`
- `REQ-009`
- `REQ-010`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `96e9cbe4ff83e48d28032c31af2837df50ce3bf77728b2c6689385a2c0b34094`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `96e9cbe4ff83e48d28032c31af2837df50ce3bf77728b2c6689385a2c0b34094`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `96e9cbe4ff83e48d28032c31af2837df50ce3bf77728b2c6689385a2c0b34094`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/02_integration/app/simple/dynsmf_autoload_policy_spec.spl
mirror: doc/06_spec/02_integration/app/simple/dynsmf_autoload_policy_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/simple/dynsmf_autoload_policy_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/simple/dynsmf_autoload_policy_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/app/simple/dynsmf_autoload_policy_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 12 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/app/simple/dynsmf_autoload_policy_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'queues background compile evidence before checked autoload for missing artifacts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/simple/dynsmf_autoload_policy_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'demand-load policy: default startup loads nothing and queues nothing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/simple/dynsmf_autoload_policy_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'skip-all startup policy still yields an empty demand-load startup session' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
