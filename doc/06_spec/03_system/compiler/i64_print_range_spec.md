# i64 Full-Range Print/Format Regression Spec

> STRESS-F02 lane (2026-07-17): compiled/JIT `print`/`println` boxed every

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# i64 Full-Range Print/Format Regression Spec

STRESS-F02 lane (2026-07-17): compiled/JIT `print`/`println` boxed every

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/i64_print_range_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

STRESS-F02 lane (2026-07-17): compiled/JIT `print`/`println` boxed every
numeric argument into a tagged `RuntimeValue` before printing. That box
packs the payload into the low bits of a 64-bit word as `(payload << 3) |
tag`, so only a signed **61-bit** value round-trips (`[-2^60, 2^60)`).
`i64::MAX` (`9223372036854775807` = `0x7FFF...FFFF`) lost its top 3 bits
under `<< 3` and printed as `-1`; `2^62` (`4611686018427387904`) shifted its
one set bit past bit 63 entirely and printed as `0`. Small ints (well under
2^60) were unaffected in either execution mode; the tree-walking
interpreter was also unaffected (it uses a native Rust `Value` enum, not
the tagged `RuntimeValue`).

Fixed by routing `TypeId::I64` print arguments through a new
`rt_raw_i64_to_string` bypass (mirrors the existing `u64` bypass) instead of
the lossy `BoxInt` path, at seed commit 5c71ca50c00. See
doc/08_tracking/bug/stress_f02_i64_boxing_truncation_2026-07-17.md.

This spec is a pure-Simple regression guard: it exercises `.to_string()` /
string interpolation over the exact boundary values called out in the bug
report (i64::MAX, i64::MIN, 2^62, and an ordinary small int) and asserts the
resulting text is exact, not truncated/sign-flipped/zeroed. It imports
nothing from src/compiler or app.io so it runs standalone under any
execution mode (interpreted or compiled/JIT).

## Scenarios

### i64 full-range print/format (STRESS-F02 regression)

#### formats i64::MAX (9223372036854775807) exactly, not -1

- formats i64::MAX (9223372036854775807) exactly, not -1


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("formats i64::MAX (9223372036854775807) exactly, not -1")
val max_val: i64 = 9223372036854775807
val text_val = "{max_val}"
assert_equal(text_val, "9223372036854775807")
assert_not_equal(text_val, "-1")
```

</details>

#### formats i64::MIN (-9223372036854775808) exactly

- formats i64::MIN (-9223372036854775808) exactly


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("formats i64::MIN (-9223372036854775808) exactly")
val min_val: i64 = -9223372036854775807 - 1
val text_val = "{min_val}"
assert_equal(text_val, "-9223372036854775808")
```

</details>

#### formats 2^62 (4611686018427387904) exactly, not 0

- formats 2^62 (4611686018427387904) exactly, not 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("formats 2^62 (4611686018427387904) exactly, not 0")
val big_val: i64 = 4611686018427387904
val text_val = "{big_val}"
assert_equal(text_val, "4611686018427387904")
assert_not_equal(text_val, "0")
```

</details>

#### formats an ordinary small int unaffected by the boxing boundary

- formats an ordinary small int unaffected by the boxing boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("formats an ordinary small int unaffected by the boxing boundary")
val small_val: i64 = 42
val text_val = "{small_val}"
assert_equal(text_val, "42")
```

</details>

#### formats a value just outside the 61-bit box range (2^60) exactly

- formats a value just outside the 61-bit box range (2^60) exactly


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("formats a value just outside the 61-bit box range (2^60) exactly")
val boundary_val: i64 = 1152921504606846976
val text_val = "{boundary_val}"
assert_equal(text_val, "1152921504606846976")
```

</details>

#### to_string() agrees with interpolation for i64::MAX

- to_string() agrees with interpolation for i64::MAX


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("to_string() agrees with interpolation for i64::MAX")
val max_val: i64 = 9223372036854775807
assert_equal(max_val.to_string(), "9223372036854775807")
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c691240748dba9fb59e47c5d0628063d686afd6c4c3d561393cc8a722d4e6e18`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c691240748dba9fb59e47c5d0628063d686afd6c4c3d561393cc8a722d4e6e18`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c691240748dba9fb59e47c5d0628063d686afd6c4c3d561393cc8a722d4e6e18`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/compiler/i64_print_range_spec.spl
mirror: doc/06_spec/03_system/compiler/i64_print_range_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/i64_print_range_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/i64_print_range_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/i64_print_range_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats i64::MAX (9223372036854775807) exactly, not -1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/i64_print_range_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats i64::MIN (-9223372036854775808) exactly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/i64_print_range_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats 2^62 (4611686018427387904) exactly, not 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
