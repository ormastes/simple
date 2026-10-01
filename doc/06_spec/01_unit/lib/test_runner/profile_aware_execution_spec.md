# Profile Aware Execution Specification

> Tests covering --profile= flag parsing (test runner), profile resolution order (CLI > simple.sdn [lints] profile= > engine default), the simple.sdn tier reads the canonical lints.profile form (WP-4), propagate_env_vars lands the resolved profile in SIMPLE_SAFETY_PROFILE, severity mapping stays consistent end-to-end (no lint-main import).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Profile Aware Execution Specification

## Scenarios

### --profile= flag parsing (test runner)

#### the 4 current tier names

#### accepts moderate

- accepts moderate
   - Expected: normalize_profile_name("moderate") equals `moderate`
   - Expected: options.profile equals `moderate`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts moderate")
expect(normalize_profile_name("moderate")).to_equal("moderate")
val options = parse_test_args(["--profile=moderate"])
expect(options.profile).to_equal("moderate")
```

</details>

#### accepts strict

- accepts strict
   - Expected: normalize_profile_name("strict") equals `strict`
   - Expected: options.profile equals `strict`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts strict")
expect(normalize_profile_name("strict")).to_equal("strict")
val options = parse_test_args(["--profile=strict"])
expect(options.profile).to_equal("strict")
```

</details>

#### accepts robust

- accepts robust
   - Expected: normalize_profile_name("robust") equals `robust`
   - Expected: options.profile equals `robust`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts robust")
expect(normalize_profile_name("robust")).to_equal("robust")
val options = parse_test_args(["--profile=robust"])
expect(options.profile).to_equal("robust")
```

</details>

#### accepts critical

- accepts critical
   - Expected: normalize_profile_name("critical") equals `critical`
   - Expected: options.profile equals `critical`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts critical")
expect(normalize_profile_name("critical")).to_equal("critical")
val options = parse_test_args(["--profile=critical"])
expect(options.profile).to_equal("critical")
```

</details>

#### a deprecated alias

#### normalizes reliable onto robust

- normalizes reliable onto robust
   - Expected: normalize_profile_name("reliable") equals `robust`
   - Expected: options.profile equals `robust`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("normalizes reliable onto robust")
expect(normalize_profile_name("reliable")).to_equal("robust")
val options = parse_test_args(["--profile=reliable"])
expect(options.profile).to_equal("robust")
```

</details>

#### an unknown profile name

#### is rejected by test_args_validation_error with a clear message

- is rejected by test_args_validation_error with a clear message


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is rejected by test_args_validation_error with a clear message")
val err = test_args_validation_error(["--profile=not-a-real-profile"])
expect(err).to_contain("invalid value for --profile")
```

</details>

#### normalize_profile_name returns empty for garbage, never crashes

- normalize_profile_name returns empty for garbage, never crashes
   - Expected: normalize_profile_name("not-a-real-profile") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("normalize_profile_name returns empty for garbage, never crashes")
expect(normalize_profile_name("not-a-real-profile")).to_equal("")
```

</details>

#### space-separated form

#### parses --profile <name> with a following token

- parses --profile <name> with a following token
   - Expected: options.profile equals `critical`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses --profile <name> with a following token")
val options = parse_test_args(["--profile", "critical"])
expect(options.profile).to_equal("critical")
```

</details>

#### missing-value form is rejected

- missing-value form is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("missing-value form is rejected")
val err = test_args_validation_error(["--profile"])
expect(err).to_contain("missing value for --profile")
```

</details>

### profile resolution order (CLI > simple.sdn [lints] profile= > engine default)

#### CLI flag wins when set

- CLI flag wins when set
   - Expected: resolve_effective_profile(options) equals `critical`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("CLI flag wins when set")
val options = parse_test_args(["--profile=critical"])
expect(resolve_effective_profile(options)).to_equal("critical")
```

</details>

#### falls back to \

- falls back to \
   - Expected: options.profile equals ``
   - Expected: resolve_effective_profile(options) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("falls back to \")
val options = parse_test_args([])
expect(options.profile).to_equal("")
# This repo's cwd during `bin/simple test` has no simple.sdn at the
# root (verified), so the sdn tier of resolution also yields "".
expect(resolve_effective_profile(options)).to_equal("")
```

</details>

### the simple.sdn tier reads the canonical lints.profile form (WP-4)

#### resolves lints.profile to critical when the key is present

- resolves lints.profile to critical when the key is present
   - Expected: read_sdn_lints_profile("test/fixtures/project_sdn_profile/with_profile/simple.sdn") equals `critical`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("resolves lints.profile to critical when the key is present")
expect(read_sdn_lints_profile("test/fixtures/project_sdn_profile/with_profile/simple.sdn")).to_equal("critical")
```

</details>

#### resolves to \

- resolves to \
   - Expected: read_sdn_lints_profile("test/fixtures/project_sdn_profile/without_profile/simple.sdn") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("resolves to \")
expect(read_sdn_lints_profile("test/fixtures/project_sdn_profile/without_profile/simple.sdn")).to_equal("")
```

</details>

#### no longer accepts the removed TOML-ish [lints] shape

- no longer accepts the removed TOML-ish [lints] shape
   - Expected: read_sdn_lints_profile("test/fixtures/project_sdn_profile/legacy_toml/simple.sdn") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("no longer accepts the removed TOML-ish [lints] shape")
expect(read_sdn_lints_profile("test/fixtures/project_sdn_profile/legacy_toml/simple.sdn")).to_equal("")
```

</details>

### propagate_env_vars lands the resolved profile in SIMPLE_SAFETY_PROFILE

#### sets SIMPLE_SAFETY_PROFILE=critical when --profile=critical is resolved

- sets SIMPLE_SAFETY_PROFILE=critical when --profile=critical is resolved
   - Expected: rt_env_get("SIMPLE_SAFETY_PROFILE") equals `critical`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("sets SIMPLE_SAFETY_PROFILE=critical when --profile=critical is resolved")
rt_env_set("SIMPLE_SAFETY_PROFILE", "")
val options = parse_test_args(["--profile=critical"])
propagate_env_vars(options)
expect(rt_env_get("SIMPLE_SAFETY_PROFILE")).to_equal("critical")
rt_env_set("SIMPLE_SAFETY_PROFILE", "")
```

</details>

#### sets SIMPLE_SAFETY_PROFILE=robust when --profile=robust is resolved

- sets SIMPLE_SAFETY_PROFILE=robust when --profile=robust is resolved
   - Expected: rt_env_get("SIMPLE_SAFETY_PROFILE") equals `robust`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("sets SIMPLE_SAFETY_PROFILE=robust when --profile=robust is resolved")
rt_env_set("SIMPLE_SAFETY_PROFILE", "")
val options = parse_test_args(["--profile=robust"])
propagate_env_vars(options)
expect(rt_env_get("SIMPLE_SAFETY_PROFILE")).to_equal("robust")
rt_env_set("SIMPLE_SAFETY_PROFILE", "")
```

</details>

#### leaves SIMPLE_SAFETY_PROFILE untouched when no profile resolves (today's behavior)

- leaves SIMPLE_SAFETY_PROFILE untouched when no profile resolves (today's behavior)
   - Expected: rt_env_get("SIMPLE_SAFETY_PROFILE") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("leaves SIMPLE_SAFETY_PROFILE untouched when no profile resolves (today's behavior)")
rt_env_set("SIMPLE_SAFETY_PROFILE", "")
val options = parse_test_args([])
propagate_env_vars(options)
expect(rt_env_get("SIMPLE_SAFETY_PROFILE")).to_equal("")
```

</details>

### severity mapping stays consistent end-to-end (no lint-main import)

#### critical resolves to Deny via the same env knob propagate_env_vars sets

- critical resolves to Deny via the same env knob propagate_env_vars sets
   - Expected: safety_pass_severity() equals `SafetyPassSeverity.Deny`
   - Expected: safety_pass_severity_for_name(options.profile) equals `SafetyPassSeverity.Deny`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("critical resolves to Deny via the same env knob propagate_env_vars sets")
rt_env_set("SIMPLE_SAFETY_PROFILE", "")
val options = parse_test_args(["--profile=critical"])
propagate_env_vars(options)
expect(safety_pass_severity()).to_equal(SafetyPassSeverity.Deny)
expect(safety_pass_severity_for_name(options.profile)).to_equal(SafetyPassSeverity.Deny)
rt_env_set("SIMPLE_SAFETY_PROFILE", "")
```

</details>

#### robust resolves to Warn (migration window, never Deny)

- robust resolves to Warn (migration window, never Deny)
   - Expected: safety_pass_severity() equals `SafetyPassSeverity.Warn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("robust resolves to Warn (migration window, never Deny)")
rt_env_set("SIMPLE_SAFETY_PROFILE", "")
val options = parse_test_args(["--profile=robust"])
propagate_env_vars(options)
expect(safety_pass_severity()).to_equal(SafetyPassSeverity.Warn)
rt_env_set("SIMPLE_SAFETY_PROFILE", "")
```

</details>

#### moderate and strict stay Advisory (no build impact)

- moderate and strict stay Advisory (no build impact)
   - Expected: safety_pass_severity() equals `SafetyPassSeverity.Advisory`
   - Expected: safety_pass_severity() equals `SafetyPassSeverity.Advisory`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("moderate and strict stay Advisory (no build impact)")
rt_env_set("SIMPLE_SAFETY_PROFILE", "")
val moderate_options = parse_test_args(["--profile=moderate"])
propagate_env_vars(moderate_options)
expect(safety_pass_severity()).to_equal(SafetyPassSeverity.Advisory)
rt_env_set("SIMPLE_SAFETY_PROFILE", "")

val strict_options = parse_test_args(["--profile=strict"])
propagate_env_vars(strict_options)
expect(safety_pass_severity()).to_equal(SafetyPassSeverity.Advisory)
rt_env_set("SIMPLE_SAFETY_PROFILE", "")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/test_runner/profile_aware_execution_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering --profile= flag parsing (test runner), profile resolution order (CLI > simple.sdn [lints] profile= > engine default), the simple.sdn tier reads the canonical lints.profile form (WP-4), propagate_env_vars lands the resolved profile in SIMPLE_SAFETY_PROFILE, severity mapping stays consistent end-to-end (no lint-main import).
- --profile= flag parsing (test runner)
- profile resolution order (CLI > simple.sdn [lints] profile= > engine default)
- the simple.sdn tier reads the canonical lints.profile form (WP-4)
- propagate_env_vars lands the resolved profile in SIMPLE_SAFETY_PROFILE
- severity mapping stays consistent end-to-end (no lint-main import)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-MC-012`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `56bc3aaa91f14a7f6228fc5e06177f61cd118f1566b880afc548837f8c9049b3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `56bc3aaa91f14a7f6228fc5e06177f61cd118f1566b880afc548837f8c9049b3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `56bc3aaa91f14a7f6228fc5e06177f61cd118f1566b880afc548837f8c9049b3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/test_runner/profile_aware_execution_spec.spl
mirror: doc/06_spec/01_unit/lib/test_runner/profile_aware_execution_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/test_runner/profile_aware_execution_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/test_runner/profile_aware_execution_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/test_runner/profile_aware_execution_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/test_runner/profile_aware_execution_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts moderate' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/test_runner/profile_aware_execution_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts strict' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/test_runner/profile_aware_execution_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts robust' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
