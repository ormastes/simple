# f64 loses low 3 mantissa bits through a RuntimeValue tagged slot (arrays/dicts) — inline tagged-float box

- **id:** seed_f64_array_element_precision_mask_2026-07-19
- **status:** open
- **severity:** high (silent miscompile — any `[f64]` element read back wrong)
- **class:** tag-box `<<3`/`>>3` — the **store-side, representation-level** cousin
  of the enum-payload f64 mask fixed in `fc7cdcb0b90`. NOT the same shape of fix.
- **found on:** the deployed `bin/simple`
  (`bin/release/x86_64-unknown-linux-gnu/simple`), which is currently the **Rust
  bootstrap seed** — today's shipping tool.

## Symptom (verified by running)

An `f64` read back out of an array is corrupted: `arr[0] == 0.1` is false.
Confirmed for a **typed `[f64]` parameter** (not just untyped literals). Scalar
`f64` (param/local) is correct — the loss is specific to values routed through a
heterogeneous RuntimeValue slot.

Repro (typed `[f64]` param), deployed seed → **rc=40** (expected 30):

```simple
fn first(xs: [f64]) -> f64:
    return xs[0]

fn main() -> i64:
    val a = [0.1, 0.2, 0.3]
    if first(a) == 0.1: return 30
    return 40
```

Control (scalar f64) → rc=30 (correct):

```simple
fn ident(v: f64) -> f64: return v
fn main() -> i64:
    if ident(0.1) == 0.1: return 30
    return 40
```

## Root cause (read from codegen — the loss is at STORE, not extract)

Array/tuple/dict literals box every native element uniformly into tagged
RuntimeValue slots (`mir/lower/lowering_expr_collection.rs:18,36`: F32/F64 →
`MirInst::BoxFloat`). The compiled `BoxFloat`
(`codegen/instr/mod.rs:1388`) is an **inline tagged float**:

```
payload = (bits >> 3) << 3      // ZEROES the low 3 mantissa bits
boxed   = payload | 2           // TAG_FLOAT = 0b010
```

So a value with nonzero low 3 bits (0.1) **loses those bits at box time**.
`UnboxFloat` (`codegen/instr/mod.rs:1439`, `(val>>3)<<3` then bitcast) is a
faithful inverse — it clears the tag and reinterprets — but the 3 bits are
already gone. **The loss is upstream, at BoxFloat.** This is the inherent cost of
stealing 3 low bits for the tag in the inline representation.

This is why the enum-payload fix does NOT apply here: enum single-field payloads
are stored **raw** (no BoxFloat) in a full 64-bit slot, so removing a spurious
extract-mask sufficed. Array/dict elements share a uniform tagged slot and are
genuinely BoxFloat'd, so an extract-side `Cast` would NOT recover the lost bits
(and, without a matching store change, would corrupt the round-trip). **The
earlier "Cast-at-extract" sketch was wrong.**

## Scope

Affects any f64 routed through a heterogeneous RuntimeValue slot: array
elements (confirmed), and by construction dict values and other ANY-channel f64.
**Open discrepancy (needs a rebuild to trace):** in a MIR-interpreter probe
`{"a":0.1}["a"] == 0.1` came back *correct* while `[0.1][0]` did not — dict-value
and array-element paths, or interp-vs-codegen `BoxFloat` semantics, differ. Do
not assume all containers behave the same until re-run.

## Fix direction (representation change — needs a design decision, not a patch)

The low bits are destroyed at box, so the fix is store-side:
1. **Heap-box f64 elements** — store a tagged *pointer* to a heap f64 (full
   precision), `UnboxFloat`/extract loads from the heap. Lossless; allocates.
   Smallest correctness-preserving change; make `BoxFloat` (and its unbox) heap
   the value instead of inline-masking.
2. **Typed untagged `[f64]` arrays** — homogeneous raw-f64 backing store, no
   per-element tag. Faster, larger change (typed-array runtime + element ops).

Either touches `BoxFloat`/`UnboxFloat` together (and every f64 extract site:
`lowering_stmt.rs` for-in ~1616, direct index, struct field
`lowering_expr_struct.rs:609`, etc.). Verifying needs a seed rebuild — **blocked
on disk** (156M free at time of filing). Do NOT ship a one-site extract patch.

## Regression guard

Add a `[f64]` element precision case (assert `[0.1][0] == 0.1`) once fixed —
mirror `test/01_unit/compiler/codegen/enum_f64_payload_precision_spec.spl`.
