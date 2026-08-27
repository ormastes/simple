# dynSMF Session Unload Reload System Specification

> Verifies the selected low_dependency_ui_dynsmf dynSMF lifecycle at the system boundary. The spec covers default stdlib-like autoload, per-id opt-out, and the interpreter-testable unload/stale/reload behavior needed for every selected stdlib-like dynSMF library to test itself without retaining stale session state.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# dynSMF Session Unload Reload System Specification

Verifies the selected low_dependency_ui_dynsmf dynSMF lifecycle at the system boundary. The spec covers default stdlib-like autoload, per-id opt-out, and the interpreter-testable unload/stale/reload behavior needed for every selected stdlib-like dynSMF library to test itself without retaining stale session state.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | doc/02_requirements/nfr/low_dependency_ui_dynsmf.md |
| Plan | doc/03_plan/sys_test/low_dependency_ui_dynsmf_dynsmf_session.md |
| Design | doc/05_design/low_dependency_ui_dynsmf.md |
| Research | doc/01_research/local/low_dependency_ui_dynsmf.md |
| Source | `test/03_system/stdlib/dynload/dynsmf_session_unload_reload_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies the selected low_dependency_ui_dynsmf dynSMF lifecycle at the system
boundary. The spec covers default stdlib-like autoload, per-id opt-out, and the
interpreter-testable unload/stale/reload behavior needed for every selected
stdlib-like dynSMF library to test itself without retaining stale session state.

## Examples

Default startup autoloads all six selected stdlib-like precompiled SMF
libraries through the SMF dynlib facade after validating the generated
`build/dynsmf/*.smf` artifacts. A per-id disable policy skips only the named
entries. Unloading any selected default library makes symbol lookup stale until
autoload reloads it with a newer generation.

**Requirements:** doc/02_requirements/feature/low_dependency_ui_dynsmf.md
**Requirements:** doc/02_requirements/nfr/low_dependency_ui_dynsmf.md
**Traceability:** REQ-004, REQ-005, REQ-006, REQ-007, REQ-008, REQ-009, REQ-010, NFR-003, NFR-005, NFR-006
**Plan:** doc/03_plan/sys_test/low_dependency_ui_dynsmf_dynsmf_session.md
**Design:** doc/05_design/low_dependency_ui_dynsmf.md
**Research:** doc/01_research/local/low_dependency_ui_dynsmf.md

## Scenarios

### low dependency UI dynSMF session lifecycle

#### autoloads the six selected stdlib-like precompiled SMF libraries by default

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- autoloads the six selected stdlib-like precompiled SMF libraries by default
   - Expected: manifest.len() equals `6`
   - Expected: dynsmf_build_plans_ready(plans) is true
   - Expected: dynsmf_artifacts_ready(manifest) is true
   - Expected: session.loaded.len() equals `6`
   - Expected: session.loaded[0].id equals `file_io`
   - Expected: session.loaded[5].id equals `tui_renderer`
   - Expected: session.evidence[0].reason equals `smf_dlopen`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("autoloads the six selected stdlib-like precompiled SMF libraries by default")
val manifest = dynsmf_default_manifest()
val plans = dynsmf_build_plans(manifest)
expect(manifest.len()).to_equal(6)
expect(dynsmf_build_plans_ready(plans)).to_equal(true)
expect(dynsmf_artifacts_ready(manifest)).to_equal(true)

val session = dynsmf_session_autoload_checked(dynsmf_session_new("system-default", dynsmf_policy_default()), manifest)
expect(session.loaded.len()).to_equal(6)
expect(session.loaded[0].id).to_equal("file_io")
expect(session.loaded[5].id).to_equal("tui_renderer")
expect(session.evidence[0].reason).to_equal("smf_dlopen")
```

</details>

#### honors per-library dynSMF disable policy while loading other defaults

- honors per-library dynSMF disable policy while loading other defaults
   - Expected: session.loaded.len() equals `4`
   - Expected: session.evidence[3].library_id equals `web_renderer`
   - Expected: session.evidence[3].action equals `skip`
   - Expected: session.evidence[5].library_id equals `tui_renderer`
   - Expected: session.evidence[5].action equals `skip`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("honors per-library dynSMF disable policy while loading other defaults")
val manifest = dynsmf_default_manifest()
val policy = dynsmf_policy_from_args_env(["--disable-dynsmf=web_renderer,tui_renderer"], "", "")
val session = dynsmf_session_autoload(dynsmf_session_new("system-disable", policy), manifest)
expect(session.loaded.len()).to_equal(4)
expect(session.evidence[3].library_id).to_equal("web_renderer")
expect(session.evidence[3].action).to_equal("skip")
expect(session.evidence[5].library_id).to_equal("tui_renderer")
expect(session.evidence[5].action).to_equal("skip")
```

</details>

#### unloads records stale symbol evidence and reloads with a newer generation

- unloads records stale symbol evidence and reloads with a newer generation
   - Expected: before.status equals `ok`
   - Expected: with_stale.evidence[7].action equals `symbol`
   - Expected: with_stale.evidence[7].status equals `stale`
   - Expected: with_stale.evidence[7].reason equals `unloaded`
   - Expected: after.status equals `ok`
   - Expected: reloaded.evidence[8].action equals `reload`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("unloads records stale symbol evidence and reloads with a newer generation")
val manifest = dynsmf_default_manifest()
val loaded = dynsmf_session_autoload(dynsmf_session_new("system-reload", dynsmf_policy_default()), manifest)
val before = dynsmf_session_symbol(loaded, "tui_renderer", "render_tui_tree")
expect(before.status).to_equal("ok")

val unloaded = dynsmf_session_unload(loaded, "tui_renderer")
val with_stale = dynsmf_session_record_symbol(unloaded, "tui_renderer", "render_tui_tree")
expect(with_stale.evidence[7].action).to_equal("symbol")
expect(with_stale.evidence[7].status).to_equal("stale")
expect(with_stale.evidence[7].reason).to_equal("unloaded")

val reloaded = dynsmf_session_autoload(with_stale, manifest)
val after = dynsmf_session_symbol(reloaded, "tui_renderer", "render_tui_tree")
expect(after.status).to_equal("ok")
expect(after.generation).to_be_greater_than(before.generation)
expect(reloaded.evidence[8].action).to_equal("reload")
```

</details>

#### unloads and reloads every selected default dynSMF library

- unloads and reloads every selected default dynSMF library
   - Expected: before.status equals `ok`
   - Expected: stale.status equals `stale`
   - Expected: stale.reason equals `unloaded`
   - Expected: after.status equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("unloads and reloads every selected default dynSMF library")
val manifest = dynsmf_default_manifest()
var session = dynsmf_session_autoload_checked(dynsmf_session_new("system-all-reload", dynsmf_policy_default()), manifest)
val ids = ["file_io", "net_io", "render2d", "web_renderer", "gui_renderer", "tui_renderer"]
val symbols = ["open", "connect", "draw", "render_html", "render_gui", "render_tui_tree"]

var idx = 0
while idx < ids.len():
    val id = ids[idx]
    val symbol = symbols[idx]
    val before = dynsmf_session_symbol(session, id, symbol)
    expect(before.status).to_equal("ok")

    val unloaded = dynsmf_session_unload(session, id)
    val stale = dynsmf_session_symbol(unloaded, id, symbol)
    expect(stale.status).to_equal("stale")
    expect(stale.reason).to_equal("unloaded")

    val reloaded = dynsmf_session_autoload_checked(unloaded, manifest)
    val after = dynsmf_session_symbol(reloaded, id, symbol)
    expect(after.status).to_equal("ok")
    expect(after.generation).to_be_greater_than(before.generation)
    session = reloaded
    idx = idx + 1
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/nfr/low_dependency_ui_dynsmf.md`
- **Plan:** `doc/03_plan/sys_test/low_dependency_ui_dynsmf_dynsmf_session.md`
- **Design:** `doc/05_design/low_dependency_ui_dynsmf.md`
- **Research:** `doc/01_research/local/low_dependency_ui_dynsmf.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-004`
- `REQ-005`
- `REQ-006`
- `REQ-007`
- `REQ-008`
- `REQ-009`
- `REQ-010`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `485960b49ea75286325cceefd067019edfcb3cc87b1b6d2cdc2ffddd5a2ebb4a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `485960b49ea75286325cceefd067019edfcb3cc87b1b6d2cdc2ffddd5a2ebb4a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `485960b49ea75286325cceefd067019edfcb3cc87b1b6d2cdc2ffddd5a2ebb4a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/stdlib/dynload/dynsmf_session_unload_reload_spec.spl
mirror: doc/06_spec/03_system/stdlib/dynload/dynsmf_session_unload_reload_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/stdlib/dynload/dynsmf_session_unload_reload_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/stdlib/dynload/dynsmf_session_unload_reload_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/stdlib/dynload/dynsmf_session_unload_reload_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/stdlib/dynload/dynsmf_session_unload_reload_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'autoloads the six selected stdlib-like precompiled SMF libraries by default' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/stdlib/dynload/dynsmf_session_unload_reload_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'honors per-library dynSMF disable policy while loading other defaults' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/stdlib/dynload/dynsmf_session_unload_reload_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'unloads records stale symbol evidence and reloads with a newer generation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
