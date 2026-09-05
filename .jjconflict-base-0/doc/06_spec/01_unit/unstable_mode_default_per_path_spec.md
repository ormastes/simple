# unstable_mode_default_per_path_spec

> Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# unstable_mode_default_per_path_spec

Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/unstable_mode_default_per_path_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience

Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

## Operator workflow

1. Run `bin/simple test test/01_unit/unstable_mode_default_per_path_spec.spl`.
2. Every scenario must pass; a failure is a regression in the behavior under test.

## Compatibility and limitations

Covers the behavior asserted here; platform-specific behavior is out of scope.

## Scenarios

### unstable mode per-path default

#### argument parsing records BOTH fields

#### leaves both fields false when neither flag is given

- Verify: leaves both fields false when neither flag is given
   - Expected: options.unstable_mode is false
   - Expected: options.unstable_mode_set is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: leaves both fields false when neither flag is given")
# @req: REQ-SSPEC-LOCAL-001
val options = parse_test_args(["--unit"])
expect(options.unstable_mode).to_equal(false)
expect(options.unstable_mode_set).to_equal(false)
```

</details>

#### records --unstable as an EXPLICIT true

- Verify: records --unstable as an EXPLICIT true
   - Expected: options.unstable_mode is true
   - Expected: options.unstable_mode_set is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: records --unstable as an EXPLICIT true")
# @req: REQ-SSPEC-LOCAL-001
val options = parse_test_args(["--unstable"])
expect(options.unstable_mode).to_equal(true)
expect(options.unstable_mode_set).to_equal(true)
```

</details>

#### records --no-unstable as an EXPLICIT false, not as absence

- Verify: records --no-unstable as an EXPLICIT false, not as absence
   - Expected: options.unstable_mode is false
   - Expected: options.unstable_mode_set is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: records --no-unstable as an EXPLICIT false, not as absence")
# @req: REQ-SSPEC-LOCAL-001
val options = parse_test_args(["--no-unstable"])
expect(options.unstable_mode).to_equal(false)
expect(options.unstable_mode_set).to_equal(true)
```

</details>

#### the four observed cases

#### (a) no env, no flag -> OFF

- Verify: (a) no env, no flag -> OFF
   - Expected: resolve_unstable(o.unstable_mode, o.unstable_mode_set, "") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: (a) no env, no flag -> OFF")
# @req: REQ-SSPEC-LOCAL-001
val o = parse_test_args(["--unit"])
expect(resolve_unstable(o.unstable_mode, o.unstable_mode_set, "")).to_equal(false)
```

</details>

#### (b) SIMPLE_BOOTSTRAP=1, no flag -> ON

- Verify: (b) SIMPLE_BOOTSTRAP=1, no flag -> ON
   - Expected: resolve_unstable(o.unstable_mode, o.unstable_mode_set, "1") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: (b) SIMPLE_BOOTSTRAP=1, no flag -> ON")
val o = parse_test_args(["--unit"])
expect(resolve_unstable(o.unstable_mode, o.unstable_mode_set, "1")).to_equal(true)
```

</details>

#### (c) SIMPLE_BOOTSTRAP=1 with --no-unstable -> OFF (override downward)

- Verify: (c) SIMPLE_BOOTSTRAP=1 with --no-unstable -> OFF (override downward)
   - Expected: resolve_unstable(o.unstable_mode, o.unstable_mode_set, "1") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: (c) SIMPLE_BOOTSTRAP=1 with --no-unstable -> OFF (override downward)")
val o = parse_test_args(["--no-unstable"])
expect(resolve_unstable(o.unstable_mode, o.unstable_mode_set, "1")).to_equal(false)
```

</details>

#### (d) no env, --unstable -> ON (override upward)

- Verify: (d) no env, --unstable -> ON (override upward)
   - Expected: resolve_unstable(o.unstable_mode, o.unstable_mode_set, "") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: (d) no env, --unstable -> ON (override upward)")
val o = parse_test_args(["--unstable"])
expect(resolve_unstable(o.unstable_mode, o.unstable_mode_set, "")).to_equal(true)
```

</details>

#### the runner itself resolves and REPORTS the mode

#### reads the bootstrap marker from SIMPLE_BOOTSTRAP

- Verify: reads the bootstrap marker from SIMPLE_BOOTSTRAP
   - Expected: source contains `env_get("SIMPLE_BOOTSTRAP")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: reads the bootstrap marker from SIMPLE_BOOTSTRAP")
val source = read_file("src/app/test_runner_new/test_runner_main.spl")
expect(source.contains("env_get(\"SIMPLE_BOOTSTRAP\")")).to_equal(true)
```

</details>

#### consults unstable_mode_set so an explicit flag beats the default

- Verify: consults unstable_mode_set so an explicit flag beats the default
   - Expected: source contains `if options.unstable_mode_set:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: consults unstable_mode_set so an explicit flag beats the default")
val source = read_file("src/app/test_runner_new/test_runner_main.spl")
expect(source.contains("if options.unstable_mode_set:")).to_equal(true)
```

</details>

#### prints the resolved mode and its origin

- Verify: prints the resolved mode and its origin
   - Expected: source contains `print "Unstable mode: `
   - Expected: source contains `unstable_state = if updated_options.unstable_mode`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: prints the resolved mode and its origin")
# @req: REQ-SSPEC-LOCAL-001
val source = read_file("src/app/test_runner_new/test_runner_main.spl")
# Split so this spec's own literal is not itself interpolated.
expect(source.contains("print \"Unstable mode: ")).to_equal(true)
expect(source.contains("unstable_state = if updated_options.unstable_mode")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b72d2208eea3073bab91d3e15d36ce36866c41a80a01a81005193d3da0a94ee5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b72d2208eea3073bab91d3e15d36ce36866c41a80a01a81005193d3da0a94ee5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b72d2208eea3073bab91d3e15d36ce36866c41a80a01a81005193d3da0a94ee5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/unstable_mode_default_per_path_spec.spl
mirror: doc/06_spec/01_unit/unstable_mode_default_per_path_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/unstable_mode_default_per_path_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/unstable_mode_default_per_path_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/unstable_mode_default_per_path_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/unstable_mode_default_per_path_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'leaves both fields false when neither flag is given' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/unstable_mode_default_per_path_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records --unstable as an EXPLICIT true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/unstable_mode_default_per_path_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records --no-unstable as an EXPLICIT false, not as absence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

<!-- doc06-layout-migration: Historical generated/manual evidence retained; authoritative executable source remains at test/01_unit/unstable_mode_default_per_path_spec.spl. -->
