# Native lane: optional-tuple payload extraction is broken in every consumption form

**Status: CLOSED — FIXED, verified by execution 2026-08-17.** The "pending seed
redeploy" caveat below is stale: the deployed binary now carries the fix.

Classified by CONTENT of current source, not by commit ancestry. The runtime
discrimination branch this doc describes is present at
`src/compiler_rust/compiler/src/hir/lower/stmt_lowering.rs:1396-1429`
(`enum_variant == "Some" && payload_patterns.len() == 1` ->
`If { rt_enum_id(subj) >= 0 ? rt_enum_payload(subj) : subj }`) and again at the
nested-pattern site near `:1521`.

Re-running this doc's own repro verbatim on the deployed binary
(`bin/simple run`, rc read on the line after the command, rc=0):

```
F1_SOME: x 7
G1_SOME: 5 9
```

Both rows that this doc recorded as broken are correct: the `if val Some(p)`
form no longer skips both arms, and the match form binds `5 9` instead of the
`3 3` nil sentinel. Verified on both `SIMPLE_EXECUTION_MODE=jit` and
`=interpreter`.

**Regression coverage now exists** (the doc's "regression specs cannot cover
this until the harness has a native lane" note is superseded — the fix is to
shell out to a subprocess, not to wait for a harness change):

- `test/01_unit/compiler/codegen/probe_optional_payload_extraction_jit.spl`
- `test/01_unit/compiler/codegen/native_optional_payload_extraction_class_spec.spl`

**The class-detection spec immediately found a LIVE sibling defect** in the same
family that this reproducer never reached: the bare `if val x = opt` unwrap
sugar and the `??` coalesce operator lower through
`hir/lower/expr/control.rs`'s `rt_unwrap_or_self` and have no such
discrimination branch, so a boxed `Some(99)` yields the raw enum pointer / 792
(= 99<<3) on the JIT. Filed as
`doc/08_tracking/bug/jit_optional_unwrap_sugar_boxed_some_not_unboxed_2026-08-17.md`.

---

**Original status:** ROOT-CAUSED and FIXED in the seed's HIR lowering (pending seed
redeploy to take effect in the deployed binary).

**Root cause (not tuple-specific — ALL cross-function optionals):** natively
compiled `T?`-returning functions produce the optional in the "raw migration
form" — the bare payload value, not a boxed Some enum (discriminator probe:
an `i64?` holding 41 prints wholesale as `invalid-heap:0x29`, i.e. the raw
untagged 41; a `(i64,i64)?` prints as a plain tuple pointer). The
Some-pattern CONDITION side already handles this (`rt_is_some` sniffs both
forms), but the BINDING side in `build_pattern_binding_stmts`
(`src/compiler_rust/compiler/src/hir/lower/stmt_lowering.rs`) extracted
payloads with `rt_enum_payload`, which returns NIL for any non-heap-enum
value — and NIL's runtime representation is `TAG_SPECIAL = 0b011 = 3`
(`runtime/src/value/tags.rs`), which is exactly why every corrupted binding
read `3`, the familiar nil-sentinel. This whole family (`Some(i64)` reads 3,
optional-tuple fields read 3 3) is one bug.

**Fix:** for single-payload `Some` patterns, `build_pattern_binding_stmts`
now emits a runtime discrimination branch instead of a bare
`rt_enum_payload` call:

```
if rt_enum_id(subject) >= 0:  rt_enum_payload(subject)   # boxed Some
else:                          subject                    # raw form
```

A different builtin alone (e.g. `rt_unwrap_or_self`) is NOT sufficient:
the two forms need different post-processing. Boxed int payloads are
BoxInt'd and rely on the name-keyed UnboxInt special case in MIR's
`lower_builtin_call_expr` (validated: swapping the builtin regressed a
literal `Some(99)` binding to 792 = 99<<3), while raw values must pass
through untouched. The branch keeps the boxed arm byte-identical to the
legacy path (same builtin, same expr type, same unboxing) and adds the
raw arm. Applied at both extraction sites (identifier bindings and
nested struct patterns); match arms and if-val flow through the same
helper.

**Validation (patched debug seed):** repro flips correct
(`Some(i64?)` binds 41, was 3; optional-tuple match binds 5 9, was 3 3;
boxed `Some(99)` still 99; real-enum single/multi-payload matches
unchanged), and the MQTT integration proof passes natively:
`mqtt_decode_string` round-trips cafe-accent to the exact decoded text
on the default engine. The decoded CONSUMED count check is blocked by a
separate, pre-existing mixed-tuple defect (field 1 of a `(text, i64)`
tuple — see
doc/08_tracking/bug/native_mixed_tuple_field1_statement_drop_2026-07-29.md).
Regression specs cannot cover this until the test harness has a native
lane — the spec lane runs the interpreter, where the bug never
reproduced; the repro drivers are inlined above for re-verification.

Originally: open — isolated with a 30-line repro while typing the MQTT packet
module (`mqtt/packet.spl`) for native compilation.
**Severity:** silent wrong results / silently skipped control flow on the
DEFAULT engine (`bin/simple run`, JIT/native — no interpreter fallback and no
diagnostic). Blocks the MQTT decode round-trip on the default engine even
though the module now compiles natively.

## Repro (fully typed, compiles natively, no HIR fallback)

```
fn f(flag: i64) -> (text, i64)?:
    if flag == 0:
        return nil
    ("x", 7)

fn g(flag: i64) -> (i64, i64)?:
    if flag == 0:
        return nil
    (5, 9)

fn main():
    if val Some(p) = f(1):
        print "F1_SOME: {p.0} {p.1}"
    else:
        print "F1_NONE"
    if val Some(q) = f(0):
        print "F0_SOME_BUG"
    else:
        print "F0_NONE_OK"
    match g(1):
        Some(t):
            print "G1_SOME: {t.0} {t.1}"
        nil:
            print "G1_NIL"
    val r = g(1)
    if r == nil:
        print "R_EQ_NIL"
    else:
        print "R_NOT_NIL"
```

Observed on the deployed seed (2026-07-29, `bin/simple run`, native — verified
no JIT-fallback INFO line):

| Construct | Expected | Observed |
|---|---|---|
| `if val Some(p) = f(1)` (value IS Some) | F1_SOME: x 7 | **NEITHER arm runs** — both silently skipped |
| `if val Some(q) = f(0)` (value is nil) | F0_NONE_OK | F0_NONE_OK (correct) |
| `match g(1): Some(t)` | G1_SOME: 5 9 | **G1_SOME: 3 3** — both payload fields read as 3, the nil sentinel |
| `r == nil` on a Some value | R_NOT_NIL | R_NOT_NIL (correct) |

So nil-detection works, but PAYLOAD EXTRACTION does not: the if-val-Some form
skips both branches for a genuine Some, and the match form takes the right arm
but yields sentinel-3 garbage for every field. Same family as the known
"JIT Option<i64> payload-3 == nil collision" and "?? on raw i64 corrupts"
sentinel bugs, but here the whole tuple payload is unrecoverable in every
consumption form tried. The interpreter lane extracts these payloads
correctly (verified: the same optional-tuple `== nil` check plus `.0`/`.1`
reads through the MQTT module ran correctly whenever the module fell back to
the interpreter).

## Impact example

`src/lib/nogc_sync_mut/mqtt/packet.spl` (+ mirrors) decode functions return
`(text, i64)?` / `(i64, i64)?` / `([i64], i64)?`. After typing the module so
it compiles natively (it previously fell back whole-module to the interpreter
over untyped parameters), the native encode path is byte-exact
(`mqtt_encode_string("café") -> [0, 5, 99, 97, 102, 195, 169]`), but no
caller can extract the decode results natively — the round-trip is blocked on
this defect, not on the MQTT logic, which is correct in isolation.

## Notes

- Do NOT work around by restructuring decode return contracts module-by-
  module; fix the codegen.
- Any module returning optional tuples that newly gains native compilation
  (e.g. by adding type annotations) is exposed; the interpreter fallback was
  masking this.
