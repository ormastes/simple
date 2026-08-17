# Native lane: reading field 1 of a mixed (text, i64) tuple silently drops statements

**Status:** ROOT-CAUSED and FIXED in the seed's lowering (pending seed
redeploy). TWO stacked causes, both index-blind element typing:

1. HIR: `lower_tuple_index` (numeric `.N` access) and the generic
   `lower_index` (constant `m[N]`) resolved the element type WITHOUT the
   index via `get_index_element_type`, i.e. every position got element
   0's type. On a heterogeneous tuple, field 1 was typed as field 0
   (`("x",7).1` typed text; `(1.5,2).1` typed f64), so MIR's
   type-directed unbox tail misfired: string-cast of a tag-boxed int
   left 56 = 7<<3 flowing into statements that then dropped silently;
   float-unbox of an int printed denormals. Homogeneous tuples were only
   accidentally correct. Fixed: per-index element type from
   `HirType::Tuple`/`LabeledTuple` (through one Pointer level), falling
   back to the legacy resolution for non-tuple receivers.
2. MIR: `lower_field_access_expr`'s tuple branch returned the
   `rt_tuple_get` result verbatim — construction boxes every native
   element (`BoxInt`/`BoxFloat`/`rt_value_bool`), so reads must apply
   the same type-directed unbox the index/dict read paths share. Fixed:
   route through `unbox_dict_read_result` (the helper extracted so
   tag-box fixes land in one place). This also covers labeled-tuple
   NAMED field access, which lowers through FieldAccess.

Validation (patched debug seed): repro flips (`t.1` prints 7, following
statements execute; `val n = t.1` then `{n}` prints 7; `{t.1 + 1}`
prints 8; `m[1]` prints 7); MQTT integration completes end-to-end
natively — `DECODED: [cafe-accent] CONSUMED: 7` — closing the last gap
in the packet round-trip chain; homogeneous tuple, struct field, and
text-text tuple controls byte-identical to the deployed seed; the
float-int tuple field now prints 2 instead of a denormal (intentional
behavior change, construction-side BoxFloat of int-typed literals in
tuple literals remains as designed since the literal is coerced to f64).
The optional-Some extraction fix (same file lineage) revalidated green
in combination.

Originally: open — found (and separated from the optional-extraction
bug) while validating the Some-binding fix. Pre-existing: the deployed
seed exhibits it MORE broadly than the patched debug seed.
**Severity:** silent statement drops on the DEFAULT engine — a `print`
interpolating the i64 field of a mixed tuple simply does not execute, and
inside an if-val then-block every statement FROM that point is skipped,
with control resuming after the if. No diagnostic, exit code 0.

## Repro (native `bin/simple run`, no JIT-fallback line)

```
fn plain() -> (text, i64):
    ("y", 8)

fn main():
    print "A"
    val t = ("x", 7)
    print "LOCAL1: {t.1}"    # SILENTLY DROPPED
    print "B"
    val u = plain()
    print "RET1: {u.1}"      # SILENTLY DROPPED
    print "C"
```

Patched debug seed (2026-07-30): prints A, B, C — both `.1`
interpolations vanish. Deployed seed: even worse — on a variant of this
probe every marked print vanished. Homogeneous tuples are fine:
`(i64, i64)` interpolates both fields correctly (T0=5 T1=9), and
`match Some(t)` over `(i64, i64)?` binds and prints 5 9 after the
optional-extraction fix. Only the MIXED (text, i64) tuple's non-zero
field is affected. Comparisons read garbage too: `parts.1 == 7` on a
decode result whose consumed count IS 7 evaluates false.

## Suspected locus

Tuple element typing/layout for heterogeneous tuples in the seed's
MIR/codegen: field 1's load is likely typed/boxed as the wrong element
class (text pointer vs raw i64), and the interpolation/compare path traps
or mis-lowers, with the trap surfacing as a silent skip of the remaining
statements in the enclosing block rather than an error.

## Impact

- The historical "if-val Some((text,i64)) skips BOTH branches" symptom in
  the optional-extraction bug was partly THIS: the then-branch was
  entered, but its single print interpolated `.1` and everything from
  there was dropped.
- MQTT decode round-trip: decoded VALUE is correct natively after the
  optional fix; the (value, consumed) tuple's consumed count cannot be
  read natively until this is fixed.

## Notes

- Spec-lane regression coverage is impossible today (interpreter lane is
  correct); keep the repro above for native re-verification.
- Do not conflate with the optional-extraction bug (fixed) or the
  kafka <<3 tag-box family; this one is specific to heterogeneous tuple
  field access.

## Triage evidence 2026-08-17 (read-only lane; classified by CURRENT SOURCE content, not SHA ancestry)

ALREADY-FIXED. Content: `lower_tuple_index` (src/compiler_rust/compiler/src/hir/lower/expr/access.rs:822-865) now computes a PER-INDEX element type from `HirType::Tuple`/`LabeledTuple` (through one `Pointer` level) before falling back to `get_index_element_type`, and cites this doc by name. Repro re-run on the deployed seed, verbatim, identical on both engines (jit and SIMPLE_EXECUTION_MODE=interpreter):
```
A
LOCAL1: 7
B
RET1: 8
C
```
No statement drop, no 56=7<<3. Bare-`print` variant identical.
