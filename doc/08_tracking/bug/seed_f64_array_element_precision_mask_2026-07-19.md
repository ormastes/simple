> **RESOLVED 2026-07-20 — container f64 is now heap-boxed (lossless) on BOTH
> compiler paths for the array/dict/scalar/for-in/print cases:**
> - interp / cranelift-JIT (`run`, `test`): `aa7ae5506c6` (Rust `simple_runtime`
>   crate) — also lossless for struct fields and Option payloads there.
> - native-build (self-hosted pure-Simple compiler + `runtime_native.c`): the
>   heap-box port — `rt_value_float` heap-boxes into an `RtCoreFloat`, O(1)
>   HashSet discrimination, `rt_value_as_float` dual-aware read, float dict keys
>   canonicalized to the inline form; the pure-Simple codegen
>   (`expr_dispatch.spl`) routes float box/unbox through those runtime calls.
>
> Verified on native-build: `[0.1][0]==0.1`, dict value/key, scalar, for-in,
> `print([0.1][0])`→`0.1`; int/string arrays, `0.0`/`-0.0` unaffected.
> Regression guards:
> `test/01_unit/compiler/codegen/array_f64_element_precision_spec.spl` (interp)
> and `test/03_system/native/array_f64_element_precision.spl` (native-build,
> array element + dict value).
>
> **UPDATE 2026-07-20 (later):** the struct-f64-field native case is now
> RESOLVED — the blocking struct-construct BUILDFAIL was root-fixed in
> `0faa51502fd`
> ([native_build_entry_struct_construction_buildfail_2026-07-20](native_build_entry_struct_construction_buildfail_2026-07-20.md)),
> and `Q(v: 0.1); q.v == 0.1` → rc 30 verified on native-build at origin tip.
>
> **One native-build case stays open — blocked by a SEPARATE pre-existing
> defect, NOT by float precision** (verified to fail identically on a clean
> origin-tip worktree without the port):
> - `f64?` Option payload via `.?`: the native `.?`/if-val unwrap leaks the Some
>   tag, not the payload (wrong for `i64? = 7` too) —
>   [hosted_native_option_try_unwrap_payload_leak_2026-07-19](hosted_native_option_try_unwrap_payload_leak_2026-07-19.md).
>
> **UPDATE 2026-07-20 (hardening sweep):** two store-side gaps found:
> - NATIVE (FIXED): empty `{}`/`[]` literals fix the element type at the i64
>   default, so a later f64 store heap-boxed but the read decoded via the
>   integer `>>3` arm and leaked the box POINTER (`var d = {}; d["k"] = 0.1`
>   printed 13668775811778). Fixed via `MirLowering.runtime_elem_value_type`
>   store-observed-type side-table (`expr_dispatch.spl` / `mir_lowering_stmts.spl`
>   / `method_calls_literals.spl`); guarded by rc-30 repros for f64 + i64 +
>   mixed-order f64/int through the same path. (A TEXT value through the same
>   empty-dict path SIGSEGVs — pre-existing at clean origin tip, same fault
>   site, unrelated to this fix:
>   [native_empty_dict_text_value_sigsegv_2026-07-20](native_empty_dict_text_value_sigsegv_2026-07-20.md).)
> - INTERP + JIT `run` side: **FIXED + VERIFIED 2026-07-21** (seed rebuilt and
>   redeployed same day). Re-isolation on the fresh seed showed the two sides
>   split: the pure INTERPRETER path (`SIMPLE_EXECUTION_MODE=interpreter`) was
>   already lossless for push/store after the earlier heap-box work + rebuild;
>   the remaining masker was the seed's **JIT/MIR lowering for `.push`**:
>   `needs_push_boxing` in `mir/lower/lowering_expr_method.rs` boxed
>   int/bool push args but had NO F32/F64 arm, so the raw double's bit
>   pattern hit tag decoding on read (`p.push(0.1); first(p) == 0.1` false,
>   the doc's rc-40 repro — array literals and `a[i] = 0.1` were already
>   clean there via BoxFloat → `rt_value_float`). The enum-payload array
>   builder in `lowering_expr_call.rs` had the identical gap for f64
>   payloads. Both now emit `MirInst::BoxFloat` for F32/F64.
>   Verified rc=30 on JIT AND forced-interp for: literal/push/store through a
>   typed `[f64]` param boundary, plus `Reading.Temp(v: 0.1)` enum payload.
>   Guard `test/03_system/native/array_f64_element_precision.spl` upgraded
>   from mask-immune 0.25/0.5 to mask-sensitive 0.1 for push/element-store
>   and gained a typed-`[f64]`-push case; rc=30 on run+interp. (Native-build
>   re-verification of the guard was blocked by an unrelated WC-wide
>   native-build outage — `_driver_module_name_collision not found` even for
>   hello-world, conflict-storm damage in the pure-Simple driver tree; the
>   fix does not touch the native lowering path.)
>
> The historical root analysis below is retained for reference.

---

> **UPDATE 2026-07-19 — interp/JIT path FIXED (heap-box).** The seed
> interpreter / cranelift-JIT path (`run`, `test`) now heap-boxes container
> floats (`Value::from_float` → `HeapFloat`), so `[0.1][0] == 0.1` there. See
> `fix(runtime): heap-box f64 in tagged RuntimeValue slots`. **native-build is
> now also fixed** (2026-07-20 heap-box port — array/dict/scalar/for-in/print;
> see the RESOLVED banner at the top). It self-hosts the pure-Simple compiler
> (`src/compiler/*.spl`) + links `runtime_native.c`; the port heap-boxes in
> `runtime_native.c` and routes float box/unbox in `expr_dispatch.spl` through
> `rt_value_float`/`rt_value_as_float`. Regression guards:
> `test/01_unit/compiler/codegen/array_f64_element_precision_spec.spl` (interp)
> and `test/03_system/native/array_f64_element_precision.spl` (native-build).

---

# f64 loses low 3 mantissa bits through a RuntimeValue tagged slot (arrays/dicts) — inline tagged-float box

- **id:** seed_f64_array_element_precision_mask_2026-07-19
- **status:** resolved 2026-07-20 (both paths, array/dict/scalar/for-in/print/struct-field; only the Option-payload native case remains blocked by a separate pre-existing bug — see top banner)
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
