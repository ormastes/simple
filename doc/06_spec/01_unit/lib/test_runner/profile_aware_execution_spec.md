# profile_aware_execution_spec

> Verifies the profile aware execution behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# profile_aware_execution_spec

Verifies the profile aware execution behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/test_runner/profile_aware_execution_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the profile aware execution behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### --profile= flag parsing (test runner)

#### the 4 current tier names

#### accepts moderate

- Verify: accepts moderate
   - Expected: normalize_profile_name("moderate") equals `moderate`
   - Expected: options.profile equals `moderate`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-MC-012
step("Verify: accepts moderate")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(normalize_profile_name("moderate")).to_equal("moderate")
val options = parse_test_args(["--profile=moderate"])
expect(options.profile).to_equal("moderate")
```

</details>

#### accepts strict

- Verify: accepts strict
   - Expected: normalize_profile_name("strict") equals `strict`
   - Expected: options.profile equals `strict`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-MC-012
step("Verify: accepts strict")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(normalize_profile_name("strict")).to_equal("strict")
val options = parse_test_args(["--profile=strict"])
expect(options.profile).to_equal("strict")
```

</details>

#### accepts robust

- Verify: accepts robust
   - Expected: normalize_profile_name("robust") equals `robust`
   - Expected: options.profile equals `robust`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-MC-012
step("Verify: accepts robust")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(normalize_profile_name("robust")).to_equal("robust")
val options = parse_test_args(["--profile=robust"])
expect(options.profile).to_equal("robust")
```

</details>

#### accepts critical

- Verify: accepts critical
   - Expected: normalize_profile_name("critical") equals `critical`
   - Expected: options.profile equals `critical`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-MC-012
step("Verify: accepts critical")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(normalize_profile_name("critical")).to_equal("critical")
val options = parse_test_args(["--profile=critical"])
expect(options.profile).to_equal("critical")
```

</details>

#### a deprecated alias

#### normalizes reliable onto robust

- Verify: normalizes reliable onto robust
   - Expected: normalize_profile_name("reliable") equals `robust`
   - Expected: options.profile equals `robust`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-MC-012
step("Verify: normalizes reliable onto robust")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(normalize_profile_name("reliable")).to_equal("robust")
val options = parse_test_args(["--profile=reliable"])
expect(options.profile).to_equal("robust")
```

</details>

#### an unknown profile name

#### is rejected by test_args_validation_error with a clear message

- Verify: is rejected by test_args_validation_error with a clear message


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-MC-012
step("Verify: is rejected by test_args_validation_error with a clear message")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val err = test_args_validation_error(["--profile=not-a-real-profile"])
expect(err).to_contain("invalid value for --profile")
```

</details>

#### normalize_profile_name returns empty for garbage, never crashes

- Verify: normalize_profile_name returns empty for garbage, never crashes
   - Expected: normalize_profile_name("not-a-real-profile") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-MC-012
step("Verify: normalize_profile_name returns empty for garbage, never crashes")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(normalize_profile_name("not-a-real-profile")).to_equal("")
```

</details>

#### space-separated form

#### parses --profile <name> with a following token

- Verify: parses --profile <name> with a following token
   - Expected: options.profile equals `critical`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-MC-012
step("Verify: parses --profile <name> with a following token")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val options = parse_test_args(["--profile", "critical"])
expect(options.profile).to_equal("critical")
```

</details>

#### missing-value form is rejected

- Verify: missing-value form is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-MC-012
step("Verify: missing-value form is rejected")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val err = test_args_validation_error(["--profile"])
expect(err).to_contain("missing value for --profile")
```

</details>

### profile resolution order (CLI > simple.sdn [lints] profile= > engine default)

#### CLI flag wins when set

- Verify: CLI flag wins when set
   - Expected: resolve_effective_profile(options) equals `critical`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-MC-012
step("Verify: CLI flag wins when set")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val options = parse_test_args(["--profile=critical"])
expect(resolve_effective_profile(options)).to_equal("critical")
```

</details>

#### falls back to \

- Verify: falls back to (engine default / unset) when no CLI flag and no simple.sdn is present
   - Expected: options.profile equals ``
   - Expected: resolve_effective_profile(options) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-MC-012
step("Verify: falls back to (engine default / unset) when no CLI flag and no simple.sdn is present")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val options = parse_test_args([])
expect(options.profile).to_equal("")
# This repo's cwd during `bin/simple test` has no simple.sdn at the
# root (verified), so the sdn tier of resolution also yields "".
expect(resolve_effective_profile(options)).to_equal("")
```

</details>

### the simple.sdn tier reads the canonical lints.profile form (WP-4)

#### resolves lints.profile to critical when the key is present

- Verify: resolves lints.profile to critical when the key is present
   - Expected: read_sdn_lints_profile("test/fixtures/project_sdn_profile/with_profile/simple.sdn") equals `critical`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-MC-012
step("Verify: resolves lints.profile to critical when the key is present")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(read_sdn_lints_profile("test/fixtures/project_sdn_profile/with_profile/simple.sdn")).to_equal("critical")
```

</details>

#### resolves to \

- Verify: resolves to when the manifest has no lints section
   - Expected: read_sdn_lints_profile("test/fixtures/project_sdn_profile/without_profile/simple.sdn") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-MC-012
step("Verify: resolves to when the manifest has no lints section")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(read_sdn_lints_profile("test/fixtures/project_sdn_profile/without_profile/simple.sdn")).to_equal("")
```

</details>

#### no longer accepts the removed TOML-ish [lints] shape

- Verify: no longer accepts the removed TOML-ish [lints] shape
   - Expected: read_sdn_lints_profile("test/fixtures/project_sdn_profile/legacy_toml/simple.sdn") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-MC-012
step("Verify: no longer accepts the removed TOML-ish [lints] shape")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(read_sdn_lints_profile("test/fixtures/project_sdn_profile/legacy_toml/simple.sdn")).to_equal("")
```

</details>

### propagate_env_vars lands the resolved profile in SIMPLE_SAFETY_PROFILE

#### sets SIMPLE_SAFETY_PROFILE=critical when --profile=critical is resolved

- Verify: sets SIMPLE_SAFETY_PROFILE=critical when --profile=critical is resolved
   - Expected: rt_env_get("SIMPLE_SAFETY_PROFILE") equals `critical`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-MC-012
step("Verify: sets SIMPLE_SAFETY_PROFILE=critical when --profile=critical is resolved")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
rt_env_set("SIMPLE_SAFETY_PROFILE", "")
val options = parse_test_args(["--profile=critical"])
propagate_env_vars(options)
expect(rt_env_get("SIMPLE_SAFETY_PROFILE")).to_equal("critical")
rt_env_set("SIMPLE_SAFETY_PROFILE", "")
```

</details>

#### sets SIMPLE_SAFETY_PROFILE=robust when --profile=robust is resolved

- Verify: sets SIMPLE_SAFETY_PROFILE=robust when --profile=robust is resolved
   - Expected: rt_env_get("SIMPLE_SAFETY_PROFILE") equals `robust`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-MC-012
step("Verify: sets SIMPLE_SAFETY_PROFILE=robust when --profile=robust is resolved")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
rt_env_set("SIMPLE_SAFETY_PROFILE", "")
val options = parse_test_args(["--profile=robust"])
propagate_env_vars(options)
expect(rt_env_get("SIMPLE_SAFETY_PROFILE")).to_equal("robust")
rt_env_set("SIMPLE_SAFETY_PROFILE", "")
```

</details>

#### leaves SIMPLE_SAFETY_PROFILE untouched when no profile resolves (today's behavior)

- Verify: leaves SIMPLE_SAFETY_PROFILE untouched when no profile resolves (today's behavior)
   - Expected: rt_env_get("SIMPLE_SAFETY_PROFILE") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-MC-012
step("Verify: leaves SIMPLE_SAFETY_PROFILE untouched when no profile resolves (today's behavior)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
rt_env_set("SIMPLE_SAFETY_PROFILE", "")
val options = parse_test_args([])
propagate_env_vars(options)
expect(rt_env_get("SIMPLE_SAFETY_PROFILE")).to_equal("")
```

</details>

### severity mapping stays consistent end-to-end (no lint-main import)

#### critical resolves to Deny via the same env knob propagate_env_vars sets

- Verify: critical resolves to Deny via the same env knob propagate_env_vars sets
   - Expected: safety_pass_severity() equals `SafetyPassSeverity.Deny`
   - Expected: safety_pass_severity_for_name(options.profile) equals `SafetyPassSeverity.Deny`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-MC-012
step("Verify: critical resolves to Deny via the same env knob propagate_env_vars sets")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
rt_env_set("SIMPLE_SAFETY_PROFILE", "")
val options = parse_test_args(["--profile=critical"])
propagate_env_vars(options)
expect(safety_pass_severity()).to_equal(SafetyPassSeverity.Deny)
expect(safety_pass_severity_for_name(options.profile)).to_equal(SafetyPassSeverity.Deny)
rt_env_set("SIMPLE_SAFETY_PROFILE", "")
```

</details>

#### robust resolves to Warn (migration window, never Deny)

- Verify: robust resolves to Warn (migration window, never Deny)
   - Expected: safety_pass_severity() equals `SafetyPassSeverity.Warn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-MC-012
step("Verify: robust resolves to Warn (migration window, never Deny)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
rt_env_set("SIMPLE_SAFETY_PROFILE", "")
val options = parse_test_args(["--profile=robust"])
propagate_env_vars(options)
expect(safety_pass_severity()).to_equal(SafetyPassSeverity.Warn)
rt_env_set("SIMPLE_SAFETY_PROFILE", "")
```

</details>

#### moderate and strict stay Advisory (no build impact)

- Verify: moderate and strict stay Advisory (no build impact)
   - Expected: safety_pass_severity() equals `SafetyPassSeverity.Advisory`
   - Expected: safety_pass_severity() equals `SafetyPassSeverity.Advisory`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-MC-012
step("Verify: moderate and strict stay Advisory (no build impact)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1e386c353698b78ead15bb56448754ea63c810667467903eba1d77e320139a5b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1e386c353698b78ead15bb56448754ea63c810667467903eba1d77e320139a5b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1e386c353698b78ead15bb56448754ea63c810667467903eba1d77e320139a5b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/lib/test_runner/profile_aware_execution_spec.spl
mirror: doc/06_spec/01_unit/lib/test_runner/profile_aware_execution_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/test_runner/profile_aware_execution_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/lib/test_runner/profile_aware_execution_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/test_runner/profile_aware_execution_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
