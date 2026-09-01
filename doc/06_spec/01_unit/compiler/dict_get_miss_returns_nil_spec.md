# Dict.get() Miss Returns nil Specification

> Purpose: Prove that Dict.get() miss vs stored zero.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dict.get() Miss Returns nil Specification

Purpose: Prove that Dict.get() miss vs stored zero.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #MIR-DICT-GET-MISS |
| Category | Compiler / MIR lowering |
| Difficulty | 3/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | doc/08_tracking/bug/native_dict_get_miss_returns_zero_not_nil_2026-07-28.md |
| Source | `test/01_unit/compiler/dict_get_miss_returns_nil_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Dict.get() miss vs stored zero.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### Dict.get() miss vs stored zero

#### returns nil for a missing i64 key

- returns nil for a missing i64 key
- Verify: returns nil for a missing i64 key
   - Expected: d.get("zz") == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns nil for a missing i64 key")
step("Verify: returns nil for a missing i64 key")
# @req: REQ-COMP-DICT-GET-MISS-VS-STORED-ZERO-001
var d: Dict<text, i64> = {}
d["a"] = 7
expect(d.get("zz") == nil).to_equal(true)
```

</details>

#### keeps a stored zero distinguishable from a miss

- keeps a stored zero distinguishable from a miss
- Verify: keeps a stored zero distinguishable from a miss
   - Expected: d.get("zero") == nil is false
   - Expected: d.get("absent") == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps a stored zero distinguishable from a miss")
step("Verify: keeps a stored zero distinguishable from a miss")
var d: Dict<text, i64> = {}
d["zero"] = 0
expect(d.get("zero") == nil).to_equal(false)
expect(d.get("absent") == nil).to_equal(true)
```

</details>

#### applies ?? default only on a miss

- applies ?? default only on a miss
- Verify: applies ?? default only on a miss
   - Expected: d.get("absent") ?? -77 equals `-77`
   - Expected: d.get("zero") ?? -77 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("applies ?? default only on a miss")
step("Verify: applies ?? default only on a miss")
var d: Dict<text, i64> = {}
d["zero"] = 0
expect(d.get("absent") ?? -77).to_equal(-77)
expect(d.get("zero") ?? -77).to_equal(0)
```

</details>

#### returns nil for a missing text key

- returns nil for a missing text key
- Verify: returns nil for a missing text key
   - Expected: t.get("zz") == nil is true
   - Expected: t.get("k") == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns nil for a missing text key")
step("Verify: returns nil for a missing text key")
var t: Dict<text, text> = {}
t["k"] = "yes"
expect(t.get("zz") == nil).to_equal(true)
expect(t.get("k") == nil).to_equal(false)
```

</details>

#### applies ?? default only on a miss for text values

- applies ?? default only on a miss for text values
- Verify: applies ?? default only on a miss for text values
   - Expected: t.get("zz") ?? "DEFAULT" equals `DEFAULT`
   - Expected: t.get("k") ?? "DEFAULT" equals `yes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("applies ?? default only on a miss for text values")
step("Verify: applies ?? default only on a miss for text values")
var t: Dict<text, text> = {}
t["k"] = "yes"
expect(t.get("zz") ?? "DEFAULT").to_equal("DEFAULT")
expect(t.get("k") ?? "DEFAULT").to_equal("yes")
```

</details>

#### keeps a stored true distinguishable from a miss

- keeps a stored true distinguishable from a miss
- Verify: keeps a stored true distinguishable from a miss
   - Expected: b.get("t") == nil is false
   - Expected: b.get("f") == nil is false
   - Expected: b.get("zz") == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps a stored true distinguishable from a miss")
step("Verify: keeps a stored true distinguishable from a miss")
var b: Dict<text, bool> = {}
b["t"] = true
b["f"] = false
expect(b.get("t") == nil).to_equal(false)
expect(b.get("f") == nil).to_equal(false)
expect(b.get("zz") == nil).to_equal(true)
```

</details>

#### returns the correct hit for a struct-valued dict

- returns the correct hit for a struct-valued dict
- Verify: returns the correct hit for a struct-valued dict
   - Expected: hv.x equals `3`
   - Expected: hv.y equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns the correct hit for a struct-valued dict")
step("Verify: returns the correct hit for a struct-valued dict")
var s: Dict<i64, Pt> = {}
s[1] = Pt(x: 3, y: 4)
val hit = s.get(1)
if val hv = hit:
    expect(hv.x).to_equal(3)
    expect(hv.y).to_equal(4)
else:
    assert_true(false, "expected a hit, got nil")
```

</details>

#### reproduces the OPEN f64-miss gap on the native/JIT lane (interpreter-only green here)

- reproduces the OPEN f64-miss gap on the native/JIT lane (interpreter-only green here)
- Verify: reproduces the OPEN f64-miss gap on the native/JIT lane (interpreter-only green here)
   - Expected: f.get("zz") == nil is true
   - Expected: f.get("pi") == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reproduces the OPEN f64-miss gap on the native/JIT lane (interpreter-only green here)")
step("Verify: reproduces the OPEN f64-miss gap on the native/JIT lane (interpreter-only green here)")
"""
`d.get(k)` on a MISS for `V = f64` is a documented, still-open gap
(dict_native_pitfalls.md's truth table, and the deliberate exclusion
comment at
src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:987-990):
`rt_value_as_float` cannot round-trip the flat-Option nil sentinel
`RT_NIL == 3` through a float bit pattern, so `dict_get_preserve_flat_nil`
(expr_dispatch.spl:991) deliberately does NOT guard the F64 decode arm.
Verified live 2026-08-07 with `bin/simple run` (Cranelift JIT, the
native-codegen lane -- see .claude/rules/testing.md "run and test are
DIFFERENT ENGINES"): a miss decodes to a real float bit pattern instead
of nil, so `== nil` is false. This assertion documents the CORRECT
interpreter-lane contract (which has always worked) -- it is NOT a gate
for the native lane, exactly like the miss-lane note above.
"""
var f: Dict<text, f64> = {}
f["pi"] = 3.5
expect(f.get("zz") == nil).to_equal(true)
expect(f.get("pi") == nil).to_equal(false)
```

</details>

### Dict.len() on the native lane

#### counts a local dict

- counts a local dict
- Verify: counts a local dict
   - Expected: d.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("counts a local dict")
step("Verify: counts a local dict")
var d: Dict<text, i64> = {}
d["a"] = 7
d["b"] = 0
expect(d.len()).to_equal(2)
```

</details>

#### counts a dict passed as a parameter

- counts a dict passed as a parameter
- Verify: counts a dict passed as a parameter
   - Expected: dict_len_of(d) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("counts a dict passed as a parameter")
step("Verify: counts a dict passed as a parameter")
var d: Dict<text, i64> = {}
d["a"] = 7
d["b"] = 0
expect(dict_len_of(d)).to_equal(2)
```

</details>

### Dict.get() miss decoding holds on the JIT lane (out of process)

#### passes the probe under the interpreter

- passes the probe under the interpreter
- Verify: passes the probe under the interpreter


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("passes the probe under the interpreter")
step("Verify: passes the probe under the interpreter")
# Control column. The interpreter was correct throughout, so this arm
# failing means the probe or the harness broke, not codegen.
expect(engine_stdout(_PROBE, "interpret")).to_contain(_PASS)
```

</details>

#### passes the probe under the cranelift JIT

- passes the probe under the cranelift JIT
- Verify: passes the probe under the cranelift JIT


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("passes the probe under the cranelift JIT")
step("Verify: passes the probe under the cranelift JIT")
# The arm that carries the weight: stored-zero / stored-false /
# stored-empty-text must stay distinguishable from a miss, and
# keys().len() must not report -1, when the decode arms are actually
# compiled rather than interpreted.
expect(engine_stdout(_PROBE, "jit")).to_contain(_PASS)
```

</details>

#### still observes the documented OPEN f64-miss gap under the JIT only

- still observes the documented OPEN f64-miss gap under the JIT only
- Verify: still observes the documented OPEN f64-miss gap under the JIT only


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("still observes the documented OPEN f64-miss gap under the JIT only")
step("Verify: still observes the documented OPEN f64-miss gap under the JIT only")
# This is the ENGINE-REACH CANARY, not a wish. `rt_value_as_float`
# cannot round-trip the flat-Option nil sentinel (RT_NIL == 3) through
# a float bit pattern, so dict_get_preserve_flat_nil
# (src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:991)
# deliberately does NOT guard the F64 decode arm.
#
# Measured 2026-08-09, same probe, same binary, both engines:
#   interpret -> PROBE F64MISS: true    (correct)
#   jit       -> PROBE F64MISS: false   (the open gap)
#
# Asserting BOTH answers is what proves each arm reached the engine it
# names. If the "jit" arm ever silently fell back to the interpreter,
# this example goes RED instead of quietly going vacuous.
#
# When the f64 gap is FIXED, this example must be updated to expect
# `true` on both arms -- it is a pin on current reality, not approval.
expect(engine_stdout(_PROBE, "interpret")).to_contain("PROBE F64MISS: true")
expect(engine_stdout(_PROBE, "jit")).to_contain("PROBE F64MISS: false")
```

</details>

#### rejects an unrecognised engine name instead of silently using the JIT

- rejects an unrecognised engine name instead of silently using the JIT
- Verify: rejects an unrecognised engine name instead of silently using the JIT


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects an unrecognised engine name instead of silently using the JIT")
step("Verify: rejects an unrecognised engine name instead of silently using the JIT")
# SIMPLE_EXECUTION_MODE falls back to the JIT on any unknown value, so
# a typo like "interp" would make an A/B comparison look like
# agreement between two identical JIT runs.
assert_false(is_known_engine("interp"))
assert_false(is_known_engine("native"))
assert_true(is_known_engine("jit"))
assert_true(is_known_engine("interpret"))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Research:** `doc/08_tracking/bug/native_dict_get_miss_returns_zero_not_nil_2026-07-28.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMP-DICT-GET-MISS-VS-STORED-ZERO-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `83b04ad55e6adec9872cc01017db2fde27ab51619102d2af14ada2c277aebbaa`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `83b04ad55e6adec9872cc01017db2fde27ab51619102d2af14ada2c277aebbaa`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `83b04ad55e6adec9872cc01017db2fde27ab51619102d2af14ada2c277aebbaa`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/dict_get_miss_returns_nil_spec.spl
mirror: doc/06_spec/01_unit/compiler/dict_get_miss_returns_nil_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/dict_get_miss_returns_nil_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/dict_get_miss_returns_nil_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/dict_get_miss_returns_nil_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/dict_get_miss_returns_nil_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns nil for a missing i64 key' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/dict_get_miss_returns_nil_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps a stored zero distinguishable from a miss' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/dict_get_miss_returns_nil_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'applies ?? default only on a miss' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
