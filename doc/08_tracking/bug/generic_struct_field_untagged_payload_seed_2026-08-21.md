# Generic fn returning scalar `T` yields untagged payload (value * 8) on the seed (2026-08-21)

**Found by:** A7 perf-baseline fixture authoring (`test/05_perf/compiler_hardening/wall_generic.spl`).
**Binary:** `bin/release/x86_64-unknown-linux-gnu/simple` (Rust seed, 59867576 bytes, 2026-08-21 05:10:21 +0000), `bin/simple run`.
**Status:** RESOLVED 2026-08-21 (see "Resolution" at the bottom). NARROWED 2026-08-21 (see "Re-probe" at the bottom): the defect is **JIT-only** — the tree-walk interpreter is correct for every case, including the ones this record lists as broken.

## Reproduce (smallest)
```simple
fn ident<T>(a: T) -> T:
    a
fn main():
    var ai: i64 = 0
    ai = ident(ai) + 1     # 1
    ai = ident(ai) + 1     # expected 2
    print "{ai}"
main()
```
Actual: `9` (= 1*8 + 1). Expected: `2`. Each generic call returning an i64 `T`
returns `value << 3` — the tag shift is never undone. `f64` comes back as its
raw bit pattern (prints as a denormal like `0.000…32106460970537`). `text` is
unaffected (pointer payload). Arithmetic inside the generic (`a + b`) shows the
same factor: `combine(0,1)` -> `8`, `combine(8,1)` -> `72`.

Generic struct fields show the same defect in a different coat: with
`struct Pair<T>: a: T`, `Pair(a: 5, b: 6).a` prints `<value:0x5>` and
`Pair(a: 1.5, b: 2.5).a` prints `576179277326712832`; a non-generic
`struct IPair: a: i64` prints `5` correctly.

## Consequences
- `test/05_perf/compiler_hardening/bench_generic.spl` and `wall_generic.spl`
  currently TIME a miscompile. Their numbers are still a valid regression
  baseline for wall/RSS (the guard does not check output), but any claim about
  generic-vs-mono cost from them is void until this is fixed.
- The mono lane must ship a failing-pre-fix reproduce spec plus class
  neighbours (`f64`, `bool`, enum payload `T`, `Pair<T>` field, nested
  `Pair<Pair<i64>>`) per the fixes-need-reproduce rule.


## Re-probe 2026-08-21 — narrowed to the JIT, and two listed cases no longer reproduce

Re-run on a seed rebuilt from current `src/compiler_rust`, with the SAME
fixture on both engines. The engine, not the type, is the discriminator:

| case | `run` (Cranelift JIT) | `SIMPLE_EXECUTION_MODE=interpreter` | expected |
|---|---|---|---|
| `ident(ai) + 1`, twice, `i64` | **`72`** | `2` | `2` |
| `ident(1.5)` (`f64`) | `1.5` | `1.5` | `1.5` |
| `ident(true)` (`bool`) | `true` | `true` | `true` |
| `ident("hi")` (`text`) | `hi` | `hi` | `hi` |
| `Pair(a: 5, b: 6).a` (generic field) | **`<value:0x5>`** | `5` | `5` |

Three things this changes about the record above:

1. **It is a JIT/codegen defect, not a seed-wide one.** Every case is correct
   under the interpreter. Anything that reaches this code through
   `bin/simple test` (which runs the tree-walk interpreter) is unaffected;
   only `bin/simple run` and the compiled lanes are.

2. **The `f64` claim no longer reproduces.** This record states f64 "comes back
   as its raw bit pattern (prints as a denormal)". It does not — `ident(1.5)`
   is `1.5` on both engines now. Either that was fixed since, or it was
   specific to the binary this record was filed against. Do not carry the f64
   case forward as a known-broken example without re-measuring it.

3. **`i64` is `72`, not `9`.** The record's `9` came from one chained call;
   `72` is the same defect through two (`((0 << 3) + 1) << 3` + 1). The
   shift-per-generic-call model in the record is confirmed — the value is
   re-boxed on each generic return and never unboxed, so the error compounds
   multiplicatively with call depth rather than staying a fixed offset.

So the surviving, confirmed-broken set is: **scalar `i64` through a generic
return, and a generic struct's scalar field — on the JIT only.**

**Not fixed in this pass.** The unboxing gate lives in MIR lowering
(`compiler/src/mir/lower/lowering_expr_struct.rs` / `lowering_expr_method.rs`
`needs_int_unbox`, which by its own comment "fires only for a concrete scalar"
— a generic `T` lowers to `TypeId::ANY`, so no unbox is emitted while the
callee still boxes). That is the place to start; the fix must decide whether
the contract is "generic return is boxed, caller unboxes at the instantiated
type" or "monomorphise and return raw", and apply it consistently to both the
call return and the generic field read.

**Spec status:** no spec added, per `.claude/rules/testing.md` — a spec
asserting the correct values would be RED, and belongs with the fix. Note that
a spec run under `bin/simple test` would **not** catch this defect at all,
since that harness runs the interpreter, which is correct here. Any regression
cover for this must force the JIT explicitly.


## Resolution 2026-08-21 — two missing boxing mirrors in MIR lowering

**Root cause.** Not a monomorphisation question at all, and not in
`needs_int_unbox`. A single-uppercase type parameter resolves to
`TypeId::ANY` (`compiler/src/hir/lower/type_resolver.rs:167`), so a generic
`-> T` is an `ANY` slot, and `ANY` slots are *tagged* by an existing,
deliberate contract: `HirStmt::Return`
(`compiler/src/mir/lower/lowering_stmt.rs:876`) already calls
`box_scalar_for_tagged_slot`, so the callee BOXES on the way out. The contract
is therefore "generic return is boxed, caller unboxes at the instantiated
type" — and the caller-side halves were simply absent in two places:

1. **Tagged -> raw local store had no unbox.** `HirStmt::Let` and the
   local-target arm of `HirStmt::Assign` (`lowering_stmt.rs`) both called
   `box_scalar_for_tagged_slot` and neither called its documented mirror
   `unbox_scalar_for_raw_slot` (`lowering_core.rs:1435`). The Assign arm's only
   unboxing was gated on `tagged_vregs`, a set this lowering populates for
   vregs it marked itself, which never contained the ANY-binop's re-boxed
   result. So `ai = ident(ai) + 1` stored `(v << 3)` back into a raw `i64`
   local and the error compounded per hop: `0 -> 8 -> 72`, which is exactly
   the `9`/`72` the record above reports.
2. **Raw -> tagged struct field store had no box.**
   `lower_struct_init_expr` (`lowering_expr_struct.rs`) boxed only for the
   `STRING`/`ANY` builtin-constructor special case; a normal struct's fields
   were stored raw. A generic field is declared `ANY`, i.e. a tagged slot, so
   `Pair(a: 5).a` read a raw word back through tag decoding — `<value:0x5>`
   — while non-generic `IPair.a` was fine because that slot is raw on both
   sides.

**Fix.** Add the two mirrors, reusing the existing helpers rather than new
logic: `unbox_scalar_for_raw_slot(declared, value_ty, ..)` after the box call
in the `Let` arm and in the `Assign` local arm (no-op unless the value's static
type is a tagged slot; bool is excluded there because it is tagged via
`rt_value_bool`, whose inverse is not `UnboxInt`), and
`box_scalar_for_tagged_slot(field_decl_ty, field.ty, ..)` per field in
`lower_struct_init_expr`.

Files:
- `src/compiler_rust/compiler/src/mir/lower/lowering_stmt.rs`
- `src/compiler_rust/compiler/src/mir/lower/lowering_expr_struct.rs`

**Correction to this record.** The `f64` case DOES reproduce — the re-probe
above tested only `ident(1.5)`, a single call whose result goes straight to
`print` (an ANY consumer, which decodes the tag correctly). Put it in a raw
`f64` slot and it breaks exactly like `i64`: pre-fix `af = ident(af) + 1.0`
printed a denormal, and `Pair(a: 1.5).a` printed `576179277326712832`.
Single-call-into-`print` is not a probe for this defect class.

**Evidence** (`test/fixtures/jit_differential/generic_return_scalar.spl`,
JIT lane, `SIMPLE_EXECUTION_MODE=jit`):

| case | pre-fix JIT | post-fix JIT | interpreter (both) |
|---|---|---|---|
| `ident(ai) + 1` twice, `i64` | `72` | `2` | `2` |
| `ident(af) + 1.0`, `f64` | denormal | `1.5` | `1.5` |
| `ident(true)` / `ident("hi")` | `true` / `hi` | unchanged | unchanged |
| `Pair(a: 5, b: 6).a` | `<value:0x5>` | `5` | `5` |
| `Pair(a: 1.5, b: 2.5).a` | `576179277326712832` | `1.5` | `1.5` |

**Regression cover.**
- `test/fixtures/jit_differential/generic_return_scalar.spl` plus a
  `known_good: "both"` entry in
  `scripts/check/check_jit_interpreter_differential.spl`. Full corpus after
  the fix: `unexpected failures (regressions): 0`, `known open JIT bugs
  reproduced: 0`.
- `test/01_unit/compiler/jit_generic_return_scalar_boxing_spec.spl`, mirrored
  to `test/unit/compiler/...`. It shells out, because `bin/simple test` forces
  the interpreter, which was always correct here. **It must name the engine
  explicitly** (`SIMPLE_EXECUTION_MODE=jit`): an empty prefix inherits the
  runner's exported `interpret` and the spec was 6/6 GREEN against the
  pre-fix seed — a false green this file records so the next author does not
  repeat it. With the engine pinned: pre-fix `6 total, 2 passed, 4 failed`,
  post-fix `6 total, 6 passed, 0 failed`.
