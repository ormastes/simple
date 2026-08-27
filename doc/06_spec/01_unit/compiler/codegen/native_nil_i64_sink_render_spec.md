# Tagged nil at an i64 render sink Specification

> On the JIT/native lane a tagged nil reaching an i64 sink used to print as the integer `3`, byte-identical to a legitimately stored `3` — a silent wrong answer, not a crash. Mechanism: `rt_index_get` returns `RuntimeValue::NIL` (word `3`); `UnboxInt` lowers to the TOTAL `rt_value_unbox_int`, which passes every non-`TAG_INT` word through verbatim; the raw `3` lands in an i64 vreg and `rt_raw_i64_to_string` renders it `"3"`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tagged nil at an i64 render sink Specification

On the JIT/native lane a tagged nil reaching an i64 sink used to print as the integer `3`, byte-identical to a legitimately stored `3` — a silent wrong answer, not a crash. Mechanism: `rt_index_get` returns `RuntimeValue::NIL` (word `3`); `UnboxInt` lowers to the TOTAL `rt_value_unbox_int`, which passes every non-`TAG_INT` word through verbatim; the raw `3` lands in an i64 vreg and `rt_raw_i64_to_string` renders it `"3"`.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CODEGEN-NIL-I64-SINK |
| Category | Compiler / Cranelift codegen |
| Difficulty | 4/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | doc/08_tracking/bug/native_tagged_nil_prints_as_integer_3_in_i64_sink_2026-08-18.md |
| Source | `test/01_unit/compiler/codegen/native_nil_i64_sink_render_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

On the JIT/native lane a tagged nil reaching an i64 sink used to print as the
integer `3`, byte-identical to a legitimately stored `3` — a silent wrong
answer, not a crash. Mechanism: `rt_index_get` returns `RuntimeValue::NIL`
(word `3`); `UnboxInt` lowers to the TOTAL `rt_value_unbox_int`, which passes
every non-`TAG_INT` word through verbatim; the raw `3` lands in an i64 vreg and
`rt_raw_i64_to_string` renders it `"3"`.

## Lane coverage — READ BEFORE TRUSTING A GREEN RUN

An sspec body NEVER executes under the Cranelift JIT (`describe`/`it`/`expect`
are Rust interpreter intrinsics with no codegen lowering, and a spec file has
no `fn main`). So every assertion here is made OUT OF PROCESS against a named
engine, via `engine_stdout`, over
`native_nil_i64_sink_render_jit_probe.spl`. The `interpret` column is the
ORACLE; the `jit` column is the lane under test. Both are asserted for every
case, so an arm that silently stopped reaching the engine it names goes RED
instead of going vacuously green.

## Reproduce-first evidence (measured, verbatim)

Deployed Rust seed `bin/release/x86_64-unknown-linux-gnu/simple`
(59620392 bytes, 2026-08-18 01:08:42), which does NOT carry the fix:

| case          | interpret (oracle) | jit          |
|---------------|--------------------|--------------|
| miss          | `nil`              | **`3`**      |
| hit = 7       | `7`                | `7`          |
| literal 3     | `3`                | `3`          |
| stored 3      | `3`                | `3`          |
| i64::MAX      | `9223372036854775807` | same      |
| -7            | `-7`               | `-7`         |

So `"renders a dict miss as nil under the JIT"` is RED on the pre-fix binary
and is the example that carries this file's weight.

`stored 3` is not decoration: the first fix attempt (routing a tainted operand
to `rt_opt_i64_to_string`) turned the miss green and simultaneously made the
stored 3 print `nil`. A candidate fix must satisfy BOTH columns at once, which
is why every case is asserted on both engines rather than only the miss.

Mechanism: `src/lib/nogc_sync_mut/spec/engine_probe.spl`
Pattern:   `doc/07_guide/infra/testing/spec_engine_reach.md`

## Scenarios

### i64 render sink: interpreter oracle

#### prints nil for a dict miss

- prints nil for a dict miss


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("prints nil for a dict miss")
expect(engine_stdout(_PROBE, "interpret")).to_contain("CASE_miss=nil")
```

</details>

#### prints every non-nil case as a plain integer

- prints every non-nil case as a plain integer


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("prints every non-nil case as a plain integer")
val out = engine_stdout(_PROBE, "interpret")
expect(out).to_contain("CASE_hit=7")
expect(out).to_contain("CASE_literal=3")
expect(out).to_contain("CASE_stored_three=3")
expect(out).to_contain("CASE_big=9223372036854775807")
expect(out).to_contain("CASE_neg=-7")
```

</details>

### i64 render sink under the Cranelift JIT

#### renders a dict miss as nil under the JIT

- renders a dict miss as nil under the JIT


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("renders a dict miss as nil under the JIT")
# THE reproduction. Pre-fix this reads `CASE_miss=3`.
expect(engine_stdout(_PROBE, "jit")).to_contain("CASE_miss=nil")
```

</details>

#### renders an ordinary hit unchanged under the JIT

- renders an ordinary hit unchanged under the JIT


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("renders an ordinary hit unchanged under the JIT")
expect(engine_stdout(_PROBE, "jit")).to_contain("CASE_hit=7")
```

</details>

#### renders a literal 3 as 3 under the JIT

- renders a literal 3 as 3 under the JIT


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("renders a literal 3 as 3 under the JIT")
# A literal never flows through UnboxInt, so it carries no nil
# provenance and must be untouched by the fix.
expect(engine_stdout(_PROBE, "jit")).to_contain("CASE_literal=3")
```

</details>

#### renders a STORED 3 as 3, not nil, under the JIT

- renders a STORED 3 as 3, not nil, under the JIT


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("renders a STORED 3 as 3, not nil, under the JIT")
# The case that killed the first fix attempt: a sink-side rule keyed
# off the raw word cannot tell a stored 3 from a nil, so it merely
# flipped which side was wrong (`three: nil`).
expect(engine_stdout(_PROBE, "jit")).to_contain("CASE_stored_three=3")
```

</details>

#### renders i64::MAX unchanged under the JIT

- renders i64::MAX unchanged under the JIT


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("renders i64::MAX unchanged under the JIT")
expect(engine_stdout(_PROBE, "jit")).to_contain("CASE_big=9223372036854775807")
```

</details>

#### renders a negative i64 unchanged under the JIT

- renders a negative i64 unchanged under the JIT


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("renders a negative i64 unchanged under the JIT")
expect(engine_stdout(_PROBE, "jit")).to_contain("CASE_neg=-7")
```

</details>

### JIT and interpreter agree line for line

#### produces an identical CASE_ block on both engines

- produces an identical CASE_ block on both engines
   - Expected: jit_lines equals `interp_lines`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("produces an identical CASE_ block on both engines")
val jit_lines = _case_lines(engine_stdout(_PROBE, "jit"))
val interp_lines = _case_lines(engine_stdout(_PROBE, "interpret"))
expect(jit_lines).to_equal(interp_lines)
```

</details>

#### actually collected six cases (non-vacuity)

- actually collected six cases (non-vacuity)
   - Expected: _case_count(engine_stdout(_PROBE, "interpret")) equals `6`
   - Expected: _case_count(engine_stdout(_PROBE, "jit")) equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("actually collected six cases (non-vacuity)")
# An empty string equals an empty string. Without this, a probe that
# failed to run would make the differential example vacuously green.
expect(_case_count(engine_stdout(_PROBE, "interpret"))).to_equal(6)
expect(_case_count(engine_stdout(_PROBE, "jit"))).to_equal(6)
```

</details>

#### rejects an unrecognised engine name instead of silently using the JIT

- rejects an unrecognised engine name instead of silently using the JIT


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects an unrecognised engine name instead of silently using the JIT")
# SIMPLE_EXECUTION_MODE falls back to the JIT on any unknown value, so
# a typo would make an A/B comparison compare the JIT with itself.
assert_false(is_known_engine("interp"))
assert_true(is_known_engine("jit"))
assert_true(is_known_engine("interpret"))
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

- **Research:** `doc/08_tracking/bug/native_tagged_nil_prints_as_integer_3_in_i64_sink_2026-08-18.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `32151a9c0a3bc5cc703425b664cae6dec746982ca54cf41e39792b797795c299`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `32151a9c0a3bc5cc703425b664cae6dec746982ca54cf41e39792b797795c299`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `32151a9c0a3bc5cc703425b664cae6dec746982ca54cf41e39792b797795c299`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/codegen/native_nil_i64_sink_render_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/native_nil_i64_sink_render_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/native_nil_i64_sink_render_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/native_nil_i64_sink_render_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/native_nil_i64_sink_render_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/codegen/native_nil_i64_sink_render_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prints nil for a dict miss' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/native_nil_i64_sink_render_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prints every non-nil case as a plain integer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/native_nil_i64_sink_render_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders a dict miss as nil under the JIT' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
