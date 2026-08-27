# SFM Sample Apps & Reuse

> The SFM infra ships sample feature modules that exercise the public API end-to-end: a native arg-parser app (AC-7), a runtime log-level changer (AC-8), a web-app login (AC-9), a version-control layer (AC-10), a UI Help/Info menu surfacing the version (AC-11), VERSION build integration (AC-12), and an in-repo reuse consumer distinct from the samples (AC-13).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SFM Sample Apps & Reuse

The SFM infra ships sample feature modules that exercise the public API end-to-end: a native arg-parser app (AC-7), a runtime log-level changer (AC-8), a web-app login (AC-9), a version-control layer (AC-10), a UI Help/Info menu surfacing the version (AC-11), VERSION build integration (AC-12), and an in-repo reuse consumer distinct from the samples (AC-13).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SFM |
| Category | Infrastructure |
| Status | Draft |
| Requirements | doc/04_architecture/language/simple_feature_module.md |
| Plan | N/A |
| Design | doc/05_design/simple_feature_module.md |
| Research | N/A |
| Source | `test/03_system/feature/sfm/sfm_samples_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The SFM infra ships sample feature modules that exercise the public API end-to-end:
a native arg-parser app (AC-7), a runtime log-level changer (AC-8), a web-app login
(AC-9), a version-control layer (AC-10), a UI Help/Info menu surfacing the version
(AC-11), VERSION build integration (AC-12), and an in-repo reuse consumer distinct
from the samples (AC-13).

## Key Concepts

| Concept | Description |
|---------|-------------|
| arg_parse_sample | Parses sample args via the arg-parser front-end layer |
| sfm_set_log_level | Changes the active log level at runtime, observable in output |
| web_login_attempt | Authenticates a credential; rejects invalid ones |
| vcs_status | A VCS status/commit operation consumed via the SFM infra |
| help_info_text | Help/Info menu text surfacing module + VERSION version |
| read_version_md | Build-time VERSION reader feeding manifest.version |

## Syntax

These scenarios exercise public SFM sample calls directly: `arg_parse_sample(args)`,
`sfm_set_log_level(level)`, `web_login_attempt(user, password)`, `vcs_status()`,
`help_info_text()`, `consumer_describe_module()`, and `read_version_md()`.

## Examples

The examples cover a valid login returning a token, an invalid login returning an
error message, arg parsing with `--name alice deploy`, and version text surfaced
through both Help/Info and the reuse consumer.

## Related Specifications

- [sfm_codec_spec.spl](sfm_codec_spec.spl) — manifest/codec these samples build on
- [sfm_di_authz_spec.spl](sfm_di_authz_spec.spl) — DI/authz the samples resolve through

## Scenarios

### SFM sample: arg-parser app (AC-7)

#### should parse a flag and a positional argument from sample args

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should parse a flag and a positional argument from sample args
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: parsed.get_str("name") equals `alice`
   - Expected: parsed.positionals[0] equals `deploy`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should parse a flag and a positional argument from sample args")
val parsed = arg_parse_sample(["--name", "alice", "deploy"])
expect(parsed.get_str("name")).to_equal("alice")
expect(parsed.positionals[0]).to_equal("deploy")
```

</details>

#### should expose the arg parser as a front-end layer entry

- should expose the arg parser as a front-end layer entry
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: parsed.get_bool("verbose") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose the arg parser as a front-end layer entry")
val parsed = arg_parse_sample(["--verbose"])
expect(parsed.get_bool("verbose")).to_equal(true)
```

</details>

### SFM sample: log-level changer (AC-8)

#### should change the active log level at runtime

- should change the active log level at runtime
   - Log capture: after_step
   - Evidence: log output verified by 1 expected check
   - Expected: sfm_get_log_level() equals `parse_debug_level()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should change the active log level at runtime")
sfm_set_log_level(parse_debug_level())
expect(sfm_get_log_level()).to_equal(parse_debug_level())
```

</details>

#### should switch back from debug to info

- should switch back from debug to info
   - Log capture: after_step
   - Evidence: log output verified by 1 expected check
   - Expected: sfm_get_log_level() equals `parse_info_level()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should switch back from debug to info")
sfm_set_log_level(parse_debug_level())
sfm_set_log_level(parse_info_level())
expect(sfm_get_log_level()).to_equal(parse_info_level())
```

</details>

### SFM sample: web login (AC-9)

#### should authenticate a valid credential

- should authenticate a valid credential
   - API capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should authenticate a valid credential")
match web_login_attempt("admin", "s3cret"):
    Ok(token): expect(token.len()).to_be_greater_than(0)
    Err(e): expect("valid login rejected: " + e).to_equal("ok")
```

</details>

#### should reject an invalid credential

- should reject an invalid credential
   - API capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject an invalid credential")
match web_login_attempt("admin", "wrong"):
    Ok(_):  expect("invalid login accepted").to_equal("ok")
    Err(e): expect(e.len()).to_be_greater_than(0)
```

</details>

### SFM sample: version-control layer (AC-10)

#### should report a VCS status through the SFM infra

- should report a VCS status through the SFM infra
   - Exec capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should report a VCS status through the SFM infra")
val status = vcs_status(".")
expect(status).to_contain("branch")
```

</details>

### SFM sample: UI Help/Info menu (AC-11, AC-12)

#### should surface the module info in the help menu

- should surface the module info in the help menu
   - Exec capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should surface the module info in the help menu")
val text = help_info_text()
expect(text).to_contain("SFM")
```

</details>

#### should surface a version string from VERSION in the help menu

- should surface a version string from VERSION in the help menu
   - Exec capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should surface a version string from VERSION in the help menu")
val ver = read_version_md("VERSION")
val text = help_info_text()
expect(text).to_contain(ver)
```

</details>

#### should read a non-empty version string from VERSION (AC-12)

- should read a non-empty version string from VERSION (AC-12)
   - Exec capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should read a non-empty version string from VERSION (AC-12)")
val ver = read_version_md("VERSION")
expect(ver.len()).to_be_greater_than(0)
```

</details>

### SFM reuse: in-repo consumer (AC-13)

#### should consume the public SFM API to describe a module

- should consume the public SFM API to describe a module
   - API capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should consume the public SFM API to describe a module")
val desc = consumer_describe_module()
expect(desc).to_contain("name")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/04_architecture/language/simple_feature_module.md`
- **Design:** `doc/05_design/simple_feature_module.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ca12b17f0b0102edbb434ec9eac06b8337608e92cbf44829b1edb0406f73fee2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ca12b17f0b0102edbb434ec9eac06b8337608e92cbf44829b1edb0406f73fee2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ca12b17f0b0102edbb434ec9eac06b8337608e92cbf44829b1edb0406f73fee2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/feature/sfm/sfm_samples_spec.spl
mirror: doc/06_spec/03_system/feature/sfm/sfm_samples_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/sfm/sfm_samples_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/sfm/sfm_samples_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/sfm/sfm_samples_spec.spl:79:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should parse a flag and a positional argument from sample args' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/sfm/sfm_samples_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should parse a flag and a positional argument from sample args' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/sfm/sfm_samples_spec.spl:87:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose the arg parser as a front-end layer entry' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/sfm/sfm_samples_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose the arg parser as a front-end layer entry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/sfm/sfm_samples_spec.spl:106:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should change the active log level at runtime' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/sfm/sfm_samples_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should change the active log level at runtime' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/sfm/sfm_samples_spec.spl:113:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should switch back from debug to info' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/sfm/sfm_samples_spec.spl:127:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should authenticate a valid credential' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/sfm/sfm_samples_spec.spl:135:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject an invalid credential' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
