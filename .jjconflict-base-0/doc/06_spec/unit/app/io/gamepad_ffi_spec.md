# gamepad_ffi_spec

> Purpose: this manual pins the behavior named "gamepad FFI compatibility facade" for the owning engineering team.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# gamepad_ffi_spec

Purpose: this manual pins the behavior named "gamepad FFI compatibility facade" for the owning engineering team.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/io/gamepad_ffi_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

Purpose: this manual pins the behavior named "gamepad FFI compatibility facade" for the owning engineering team.
    Audience: engineers verifying regressions in this area; steps below are executable evidence.

## Scenarios

### gamepad FFI compatibility facade

#### contains no duplicate foreign declarations

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- contains no duplicate foreign declarations


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("contains no duplicate foreign declarations")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
val source = file_read("src/app/io/gamepad_ffi.spl")
assert_false(source.contains("extern fn "))
assert_false(source.contains("@extern("))
```

</details>

#### exports the canonical safe gamepad surface explicitly

- exports the canonical safe gamepad surface explicitly


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("exports the canonical safe gamepad surface explicitly")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
val source = file_read("src/app/io/gamepad_ffi.spl")
expect(source).to_contain("export use app.io.gamepad_sffi.{{")
expect(source).to_contain("gamepad_init")
expect(source).to_contain("gamepad_stick_with_deadzone")
assert_false(source.contains("gamepad_sffi.*"))
```

</details>

#### does not re-export raw runtime symbols

- does not re-export raw runtime symbols


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("does not re-export raw runtime symbols")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
val source = file_read("src/app/io/gamepad_ffi.spl")
assert_false(source.contains("rt_gilrs_"))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3dcb40d13e1b2d046429282f6d8d96e6bbcf6a93394c0075215bc07569b0a57b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3dcb40d13e1b2d046429282f6d8d96e6bbcf6a93394c0075215bc07569b0a57b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3dcb40d13e1b2d046429282f6d8d96e6bbcf6a93394c0075215bc07569b0a57b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/unit/app/io/gamepad_ffi_spec.spl
mirror: doc/06_spec/unit/app/io/gamepad_ffi_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/io/gamepad_ffi_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/io/gamepad_ffi_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
