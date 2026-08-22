# dynSMF Startup Autoload Policy Integration Specification

> Verifies the dynsmf autoload policy behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# dynSMF Startup Autoload Policy Integration Specification

Verifies the dynsmf autoload policy behaviour end to end so maintainers of this

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
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the dynsmf autoload policy behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### dynSMF startup autoload policy

#### queues background compile evidence before checked autoload for missing artifacts

- Verify: queues background compile evidence before checked autoload for missing artifacts
   - Expected: session.loaded.len() equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: session.evidence.len() equals `4)  # oracle: pinned constant asserted by this scenario`
   - Expected: session.evidence[0].library_id equals `file_io`
   - Expected: session.evidence[0].action equals `compile_background`
   - Expected: session.evidence[0].status equals `queued`
   - Expected: session.evidence[1].library_id equals `gui_renderer`
   - Expected: session.evidence[1].action equals `compile_background`
   - Expected: session.evidence[1].status equals `queued`
   - Expected: session.evidence[2].status equals `failed`
   - Expected: session.evidence[2].reason equals `artifact_missing_file`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-005 REQ-006 REQ-007 REQ-009 REQ-010
step("Verify: queues background compile evidence before checked autoload for missing artifacts")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val manifest = [
    DynSmfManifestEntry(id: "file_io", path: "build/dynsmf/startup_missing_file_io.smf", source_module: "std.io", artifact_kind: "precompiled_smf", abi_version: "1", default_autoload: true, exports: ["open"]),
    DynSmfManifestEntry(id: "gui_renderer", path: "build/dynsmf/startup_missing_gui_renderer.smf", source_module: "app.ui.web.backend", artifact_kind: "precompiled_smf", abi_version: "1", default_autoload: true, exports: ["render_gui"])
]
val session = dynsmf_startup_session_for_manifest_from_values([], "", "", "integration-background", manifest)
expect(session.loaded.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(session.evidence.len()).to_equal(4)  # oracle: pinned constant asserted by this scenario
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

#### demand-load policy: default startup loads nothing and queues nothing

- Verify: demand-load policy: default startup loads nothing and queues nothing
   - Expected: session.loaded.len() equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: session.evidence.len() equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-005 REQ-006 REQ-007 REQ-009 REQ-010
step("Verify: demand-load policy: default startup loads nothing and queues nothing")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# Perf program 2026-08-10: the seven stdlib-like entries are
# demand-loaded, so a plain startup session performs zero loads,
# zero background-compile queueing, and zero spawns.
val session = dynsmf_startup_session_from_values([], "", "", "integration-default")
expect(session.loaded.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(session.evidence.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### skip-all startup policy still yields an empty demand-load startup session

- Verify: skip-all startup policy still yields an empty demand-load startup session
   - Expected: by_arg.loaded.len() equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: by_arg.policy.source equals `arg:--no-dynsmf`
   - Expected: by_arg.evidence.len() equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: by_env.loaded.len() equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: by_env.policy.source equals `env:SIMPLE_DYNSMF`
   - Expected: by_env.evidence.len() equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-005 REQ-006 REQ-007 REQ-009 REQ-010
step("Verify: skip-all startup policy still yields an empty demand-load startup session")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val by_arg = dynsmf_startup_session_from_values(["--no-dynsmf"], "", "", "integration-no-arg")
expect(by_arg.loaded.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(by_arg.policy.source).to_equal("arg:--no-dynsmf")
expect(by_arg.evidence.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario

val by_env = dynsmf_startup_session_from_values([], "0", "", "integration-no-env")
expect(by_env.loaded.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(by_env.policy.source).to_equal("env:SIMPLE_DYNSMF")
expect(by_env.evidence.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### honors per-id disable policy on an explicit autoload manifest

- Verify: honors per-id disable policy on an explicit autoload manifest
   - Expected: session.loaded.len() equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: saw_skip is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-005 REQ-006 REQ-007 REQ-009 REQ-010
step("Verify: honors per-id disable policy on an explicit autoload manifest")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val manifest = [
    DynSmfManifestEntry(id: "tui_renderer", path: "build/dynsmf/policy_tui_renderer.smf", source_module: "app.ui.render.tui_widgets", artifact_kind: "precompiled_smf", abi_version: "1", default_autoload: true, exports: ["render_tui_tree"])
]
val session = dynsmf_startup_session_for_manifest_from_values(["--disable-dynsmf=tui_renderer"], "", "", "integration-disable", manifest)
expect(session.loaded.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
var saw_skip = false
for row in session.evidence:
    if row.library_id == "tui_renderer" and row.action == "skip":
        saw_skip = true
expect(saw_skip).to_equal(true)
```

</details>

#### exposes app root dynSMF status evidence without noisy plain startup

- Verify: exposes app root dynSMF status evidence without noisy plain startup
   - Expected: plain_code equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: plain_out equals ``
   - Expected: code equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-005 REQ-006 REQ-007 REQ-009 REQ-010
step("Verify: exposes app root dynSMF status evidence without noisy plain startup")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val (plain_out, plain_err, plain_code) = run_app_root_dynsmf([])
expect(plain_code).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(plain_out).to_equal("")

val (out, err, code) = run_app_root_dynsmf(["--dynsmf-status"])
expect(code).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(out).to_contain("dynsmf session=app-root")
expect(out).to_contain("loaded=0")
```

</details>

#### exposes app root dynSMF opt-out evidence

- Verify: exposes app root dynSMF opt-out evidence
   - Expected: code equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-005 REQ-006 REQ-007 REQ-009 REQ-010
step("Verify: exposes app root dynSMF opt-out evidence")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val (out, err, code) = run_app_root_dynsmf(["--no-dynsmf", "--dynsmf-status"])
expect(code).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(out).to_contain("policy=arg:--no-dynsmf")
expect(out).to_contain("loaded=0")
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

- **Requirements:** `doc/02_requirements/nfr/low_dependency_ui_dynsmf.md`
- **Plan:** `doc/03_plan/sys_test/low_dependency_ui_dynsmf_dynsmf_session.md`
- **Design:** `doc/05_design/low_dependency_ui_dynsmf.md`
- **Research:** `doc/01_research/local/low_dependency_ui_dynsmf.md`


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fa7fc18766963b8fb1efd73fed6ab51321352891809b150556989d326943951e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fa7fc18766963b8fb1efd73fed6ab51321352891809b150556989d326943951e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fa7fc18766963b8fb1efd73fed6ab51321352891809b150556989d326943951e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/02_integration/app/simple/dynsmf_autoload_policy_spec.spl
mirror: doc/06_spec/02_integration/app/simple/dynsmf_autoload_policy_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/simple/dynsmf_autoload_policy_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/02_integration/app/simple/dynsmf_autoload_policy_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/simple/dynsmf_autoload_policy_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
