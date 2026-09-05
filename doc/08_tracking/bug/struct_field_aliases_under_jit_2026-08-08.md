# A `struct` stored in a class field ALIASES under the JIT (value semantics violated)

> ## RETIRED 2026-08-17 -- independently re-confirmed, and COLLAPSED with the class row (worker W5)
>
> Confirms the existing DID-NOT-REPRODUCE note above by execution on the DEPLOYED
> seed, with a validated control (see below). All four aliasing shapes hold the
> `struct` = value / `class` = identity contract under `interpreter` AND `jit`:
>
> ```
> A_class_in_array=777   # class: identity semantics preserved (correct)
> B_struct_from_field=0   # struct out of a class field: value-copied (correct)
> C_struct_local_copy=0   # struct local copy: value-copied (correct)
> D_struct_in_array=0     # struct out of an array: value-copied (correct)
> ```
>
> **FAMILY: this row and `jit_class_mutation_drop_characterization_2026-07-04` are ONE
> aliasing-of-boxed-object question measured by ONE probe** (case A is that row, cases
> B-D are this row). They are retired together; both directions of the F1 contract
> hold simultaneously, which is the thing neither doc could show alone.
>
> **Why this is not a false green:** an all-modes-agree result is exactly what an
> IGNORED `SIMPLE_EXECUTION_MODE` would also produce. The guard therefore carries a
> positive control -- a 61-bit boxed-int probe that MUST diverge -- and it does
> (`1152921504606846976` interpreter vs `-1152921504606846976` jit). The mode switch
> is provably live, so the agreement above is real.
>
> Regression guard: `test/01_unit/engine_divergence/check-engine-divergence-probes.shs`.


> **DID NOT REPRODUCE 2026-08-17 — closeable.** Probe on a seed built from current HEAD,
> three aliasing shapes, both engines: a struct read out of a class field
> (`copy = h.p; copy.x = 99` -> `h.p.x` = 0), a plain local copy (`b = a; b.x = 5` ->
> `a.x` = 0), and an array element (`e = arr[0]; e.x = 7` -> `arr[0].x` = 0). Value
> semantics hold in every case under `jit` and `interpreter` alike. Classified by
> execution, not by SHA ancestry.


- **Filed:** 2026-08-08
- **Status:** **CLOSED 2026-08-17 — retired, did not reproduce.** THREE independent probe
  runs now agree that value semantics hold under BOTH engines across every aliasing
  shape: the header's HEAD-seed note, worker W5's deployed-seed run with a positive
  control, and a third run recorded at the bottom of this file on a separate probe file.
  (Previously: "Open, not fixed. Root cause localized to the Rust seed …")
- **CAVEAT on W5's positive control, added 2026-08-17:** W5's guard
  (`test/01_unit/engine_divergence/check-engine-divergence-probes.shs`, probe
  `probes/boxed_int_61bit_probe.spl`) proves its mode switch is live by requiring
  `1152921504606846976` to diverge to `-1152921504606846976` under `jit`. **That
  divergence is itself a defect, and it has now been fixed** — see
  `stage3_numeric_interpolation_slot_corruption_2026-08-13.md`. Once a seed carrying
  that fix is deployed, W5's control will stop diverging and its guard will
  (correctly, fail-closed) stop passing. W5's lane needs a different liveness control;
  that file was deliberately not edited from here.
- **Severity:** High — this is the *other half* of the F1 contract. Every packed-scene design
  that relies on `struct` snapshotting (span refs, row descriptors, revision stamps) is
  engine-dependent in the opposite direction from the class defect.
- **Component:** seed JIT (Cranelift path — `bin/simple run`, and every non-`interpret`
  value of `SIMPLE_EXECUTION_MODE`)
- **Found by:** LANE F1 of `doc/03_plan/ui/perf/render_perf_redesign_plan_2026-08-06.md` § 2
- **Sibling defect:** `class_field_reference_semantics_diverge_2026-08-06.md` (interpreter
  value-copies *class* fields). This doc is a **distinct root cause direction** and is filed
  separately per the one-doc-per-root-cause rule.

## Contract under test

From the plan, § 2 / F1: **`struct` = value semantics; `class` = identity/reference
semantics.** Assigning a `struct` into a class field must copy the VALUE; later mutation of
the source must not be visible through the field.

## The divergence

Fixture: `test/fixtures/repro/compiler/class_identity/class_identity_corpus_probe.spl`
(case F, lines 108-115).

```
struct SCell:
    n: i64
class StructHolder:
    cell: SCell

var s = SCell(n: 150)
val sh = StructHolder(cell: s)
s.n = 151            # mutate the SOURCE struct
# contract: sh.cell.n == 150 (value copy)
```

| engine | `sh.cell.n` | verdict |
|---|---|---|
| `SIMPLE_EXECUTION_MODE=interpret` | 150 | VAL — contract held |
| JIT (default, `bin/simple run`) | **151** | **ALIAS — contract VIOLATED** |

Binary measured: `bin/release/x86_64-unknown-linux-gnu/simple`, the Rust bootstrap **seed**
(`bin/simple --version` prints the seed warning banner), mtime 2026-08-08 12:14.

## Why this is the mirror image of the sibling defect

Neither engine implements the contract; they each apply **one uniform aggregate policy** and
therefore fail in opposite directions:

| case | interpreter | JIT |
|---|---|---|
| class in a field / array / optional / trait field | **COPY** ❌ | REF ✅ |
| struct in a class field | VAL ✅ | **ALIAS** ❌ |

So "the JIT is the correct engine" is false, and so is "the interpreter is the correct
engine". Picking either engine as the reference implementation for F1 would ship the other
half of the bug.

## Root-cause localization

The seed carries **no struct-vs-class value-semantics distinction at all**. Anchored grep
over the 1,764 non-vendor `.rs` files in `src/compiler_rust/`:

| symbol | hits | are any about value vs reference semantics? |
|---|---|---|
| `ClassKind` | 0 | — |
| `StructKind` | 0 | — |
| `TypeKind::Struct` / `TypeKind::Class` | 0 / 0 | — |
| `value_semantics` | 0 in source (4 hits are all generated `target/**/simple_tests.rs` test-name strings) | no |
| `is_struct` | 13 | no — all vendor-adjacent or unrelated shape checks |
| `is_class` | 14 | no — coverage (`interpreter_extern/coverage.rs:76`, `mock_helper/sffi.rs:94`), method dispatch (`interpreter_method/mod.rs:176`), pattern lowering (`hir/lower/expr/control.rs:636`, `hir/lower/stmt_lowering.rs:2365`) |

There is no site that could branch a field store on declaration kind, because the
declaration kind is not carried to the store. Each backend therefore hard-codes one policy:
the tree-walk interpreter clones every aggregate on a field store, and the JIT stores every
aggregate by pointer.

## Unblock condition

A fix must (a) propagate the `struct` / `class` declaration kind into HIR/MIR field-store
lowering, and (b) make both engines branch on it. That is a cross-cutting compiler change in
the **Rust seed**, which the repo rules place out of scope for ordinary work (fix `.spl`,
not Rust) — so it is properly resolved by the pure-Simple self-hosted engines once they are
the deployed default, and the pure-Simple lowering must be built with the kind distinction
present from the start. Do not attempt a local patch in either seed backend: making the JIT
clone structs without the kind bit would clone classes too, converting this defect into the
sibling one.

## Executable pins

- `test/01_unit/compiler/class_identity_corpus_spec.spl` — the two `struct` examples assert
  the CONTRACT (not a pinned defect). They are GREEN on the interpreter, which `bin/simple
  test` uses, and would be RED on the JIT. They exist so that when the spec harness gains a
  JIT lane (see `run_vs_test_harness_divergence_2026-07-28.md`) this defect fails loudly
  instead of silently.
- `test/fixtures/repro/compiler/class_identity/class_identity_corpus_probe.spl` — prints the
  full per-engine table in one run.

## Downstream

`src/lib/nogc_sync_mut/ui/draw_ir_v3_native_writer.spl:14-19` documents the live workaround
for the *class* half. This struct half adds a second precondition for removing it: see the
"what would justify removal" note in that file and in the sibling bug doc.

---

## SECOND, INDEPENDENT CONFIRMATION 2026-08-17 — closing the row

The header's "DID NOT REPRODUCE 2026-08-17" note was written against a seed
built from HEAD by another lane. The `evidence` column and
"re-verified by source inspection" stamps in this tracker have been shown wrong
on 37% of the rows they touch, so that note alone was not treated as sufficient.
It was re-run here on a **different** binary, from a separate probe file, with
the same conclusion.

Binary: `bin/release/x86_64-unknown-linux-gnu/simple`, the Rust bootstrap seed
(`bin/simple --version` prints the seed banner), size 59536728, mtime
2026-08-16 22:59:37. Nothing was rebuilt or redeployed (~15 lanes share this
checkout).

Probe run as a subprocess under each engine — not as a spec body, because
`bin/simple test` is the tree-walk interpreter and cannot reach the cranelift
JIT at all, so a spec assertion here would be vacuous by construction:

```
struct SCell:
    var n: i64
class StructHolder:
    var cell: SCell

fn main():
    var s = SCell(n: 150)
    val sh = StructHolder(cell: s)
    s.n = 151                      # mutate the SOURCE struct
    print("FIELD={sh.cell.n}")     # contract: 150 (value copy)
    var a = SCell(n: 1)
    var b = a
    b.n = 5
    print("LOCAL={a.n}")           # contract: 1
    var arr = [SCell(n: 2)]
    var e = arr[0]
    e.n = 7
    print("ARRELEM={arr[0].n}")    # contract: 2
```

| shape | contract | `SIMPLE_EXECUTION_MODE=interpreter` | `SIMPLE_EXECUTION_MODE=jit` |
|---|---|---|---|
| struct read out of a class field | 150 | 150 VAL | 150 VAL |
| plain local copy | 1 | 1 VAL | 1 VAL |
| array element copy | 2 | 2 VAL | 2 VAL |

The `sh.cell.n == 151` alias reported in "The divergence" table above is not
reproducible on this binary in either engine. Value semantics for `struct` hold
uniformly. Classified by EXECUTION, not by SHA ancestry (rebasing rewrites SHAs
in this tree, so ancestry proves nothing here).

### Corroborating representation note

The interpreter's aggregate representation now makes the two contracts
structurally distinct rather than uniform, which is consistent with the
observed behaviour: `Value::ClassInstance(Arc<ClassInstance>)`
(`src/compiler_rust/compiler/src/value.rs:1240`) is the **only** Arc-shared
aggregate variant, documented in place as "Shared-identity class instance
storage (source `class` values)" with `fields: RwLock<HashMap<String, Value>>`
(same file, 1111-1115). A struct has no such shared handle, so cloning a struct
`Value` cannot alias. This is corroboration for the interpreter half only — the
JIT half rests on the execution result above, not on this symbol.

### What this closure does NOT cover

The **sibling** row `class_field_reference_semantics_diverge_2026-08-06.md` (the
opposite direction: the interpreter value-copying *class* fields) is a separate
root cause and is NOT addressed here. Nothing in this closure should be read as
evidence about that row.
