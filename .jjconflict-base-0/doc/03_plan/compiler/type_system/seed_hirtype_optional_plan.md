# Seed `HirType::Optional` — Scoping Result and Staged Plan

Date: 2026-07-28. Status: SCOPED, not implemented. Verdict: **the type change is
small; the semantics migration is not, and it is blocked on a prior repair.**

## Verdict

Adding `HirType::Optional { inner }` to the seed is **structurally contained** —
measured, not estimated. But it must NOT land first. The `index_of` family is
currently routed to a **runtime symbol that is unresolvable** (its definition is
unpushed, and the symbol-table generator drops it even where it exists — P4), and
four codegen paths disagree about what `index_of` even returns. Typing it
`Optional` on top of that would paper over two link-level defects with a
type-level one.

Stage 0 below is the real root fix for the reported `index_of` bug. The Optional
type is Stage 2+.

## PROVEN (measured this session)

### P1. The enum change breaks exactly 3 matches

Added `Optional { inner: TypeId }` to `HirType` in a clean worktree off
`origin/main` and ran `cargo check -p simple-compiler`. Result: **3 errors, all
`E0004` non-exhaustive**, zero others:

- `compiler/src/codegen/lean/types.rs:216`
- `compiler/src/hir/lower/type_resolver.rs:514`
- `compiler/src/hir/type_registry.rs:243`

Every other `match` on `HirType` already has a wildcard arm. Total surface:
550 `HirType::` references across 53 files, but only these 3 are exhaustive.

### P2. There is a working precedent to copy

`HirType::Promise { inner: TypeId }` is already a single-inner wrapper variant
with the exact shape needed. It has **6 references across 4 files** — that is the
realistic cost of a fully-wired single-inner variant in this codebase.

### P3. `T?` currently resolves to a shared pointer

`type_resolver.rs:314`: `Type::Optional(inner)` registers
`HirType::Pointer { kind: Shared, capability: Shared, inner }`. Indistinguishable
from a genuine shared pointer. There are 18 `PointerKind::Shared` sites and 53
`HirType::Pointer` sites to audit for which ones *mean* optional.

### P4. `rt_index_of` was unresolvable — RESOLVED 2026-07-28, see Stage 0

**This section is retained as the historical record; the two defects it describes
were both fixed at `origin/main` by `5c75a1bbce0` after it was written.** Read
Stage 0 for current state. The method note at the end still applies.

Two codegen paths emit a call to `rt_index_of`:

- `codegen/instr/closures_structs.rs:1284` — `"index_of" => "rt_index_of"`
- `codegen/instr/calls.rs:3234` — `"index_of" => Some("rt_index_of")`

An earlier revision of this plan said `rt_index_of` was "defined nowhere in the
repository". **That was measured against `origin/main` and is true there, but it
is misleading**, and a peer lane correctly challenged it. The reconciled facts,
each verified:

**Defect 1 — the definition is UNPUSHED.**
`rt_index_of` *does* exist as a receiver-polymorphic dispatcher at
`src/compiler_rust/runtime/src/value/collections.rs:3051` — it tries
`rt_array_index_of` first and falls back to `rt_string_find`, dispatching by
trial because both callees are total and return `-1` on receiver mismatch. But it
exists **only in the local working copy's HEAD** (`533d96801dd`), introduced by
`0d864c55fe7` *"fix(borrow): forward-propagate move state"* — an unrelated
borrow-checker commit that is **NOT an ancestor of `origin/main`**. On
`origin/main`, `collections.rs:3051` is a blank line and `git grep "fn
rt_index_of"` over the whole tree returns nothing.

So a fresh clone gets a compiler that emits calls to a function that is not in
its own source tree. **This is unpushed work riding in an unrelated commit** —
exactly the profile this repo has repeatedly lost to stale-working-copy clobbers.
It should be committed on its own merits, urgently, by its owner.

**Defect 2 — even where it exists, the symbol-table generator drops it.**
The JIT resolves `rt_*` through the build-script-generated
`RUNTIME_SYMBOL_ENTRIES` (`src/compiler_rust/runtime/build.rs`). Measured across
all five generated tables under
`target/release/build/simple-runtime-*/out/runtime_symbol_entries.rs`:
`rt_index_of` = **0 in every table**, while siblings `rt_array_index_of` = 2 and
`rt_string_find` = 2 in four of them. `rt_array_index_of` is declared identically
(`#[no_mangle]`, same `pub extern "C" fn` form) twenty lines earlier **in the same
file**, so the file is scanned and this one symbol is specifically dropped.
Suspect `collect_rust_file_exports` in `build.rs` (~lines 276-293); root cause not
yet chased.

Nothing registers it → the linker drops it → `nm bin/simple | grep rt_index_of` =
**0** (`rt_string_find` = 1, for contrast) → unresolvable at JIT time. This is
what produced the `unresolved external symbol 'rt_index_of'` bailout another lane
observed. Both defects are link-level, not typing-level.

### P5. `index_of` has FOUR divergent behaviours

| Path | Target | Runtime representation |
|---|---|---|
| `closures_structs.rs:1284`, `calls.rs:3234` | `rt_index_of` | the **intended unifier** (array-then-string trial dispatch), but unpushed *and* missing from the symbol table → bailout/link failure. See P4. |
| `llvm/emitter.rs:191`, `llvm/functions.rs:2274,2611` | `rt_string_find` | raw `i64`, `-1` sentinel |
| `runtime_sffi.rs:413` registers it, no method-name path selects it | `rt_string_index_of` | **real `Option`** (`rt_option_some`/`rt_option_none`) |
| `mir/lower/lowering_expr_method.rs:554` (array receiver) | `rt_array_index_of` | raw `i64`, `-1` sentinel |

So `rt_string_index_of` — the only genuinely Option-returning implementation —
appears to be **dead code no method-name dispatch reaches**.

### P6. The HIR type table already contradicts the runtime

`hir/lower/expr/mod.rs:970` types the whole string family `TypeId::I64` with the
comment *"find/rfind return -1 if not found ... raw i64 from rt_string_find"*.
`mod.rs:1036` types array `index_of` `I64` via a comment documenting a
*deliberate* workaround: typing it `I64` "restores the BoxInt and picks static
dispatch". **Retyping these to `Optional` risks reintroducing the exact misdecode
that workaround suppresses.** That is the single largest hazard in this plan.

`mod.rs:1039`: `first | last | get` return the bare element type, with the
comment "(or Option<element>)" — the gap acknowledged in-place.

### P7. The pure-Simple design is portable

`src/compiler/30.types/type_system/expr_infer.spl` uses `Optional(inner)` /
`type_Optional(inner:)` at lines 354, 366, 369, 387, 396, 415, 424, and
`40.mono/monomorphize/util.spl` (62, 212, 353) already threads it through
monomorphization including a `concretetype_Optional` bridge. The shape maps 1:1
onto `HirType::Optional { inner }`. **Port, do not reinvent.**

## INFERRED (not executed)

- That the 899 `index_of`-family `??` sites split by receiver rather than
  migrating uniformly. Follows from P5 but was not measured per-site.
- That making `??` a no-op on statically-non-Optional operands fixes the
  `-1`-sentinel sites for free (`arr.index_of(x) ?? -1` → raw `-1` when absent,
  raw index when present — both correct). Reasoned from P5, not run.
- Whether the 7,288 unclassifiable sites are dominated by genuine `T?` receivers.
  Not sampled.

## Design: why the non-zero nil sentinel forces a type-level rule

`TAG_SPECIAL = 0b011 = 3` and `rt_is_none` tests `value.0 == TAG_SPECIAL`. So
raw-`3`-is-nil holds **by construction** — swapping `??` to `rt_is_some` does not
fix it. The discriminator must be **static**, not dynamic:

- `lower_coalesce` dispatches on the operand's `HirType`. `Optional{..}` → nil
  test + unwrap. Anything else → **the operand itself**, unchanged, plus a lint.
- No new runtime representation is required. `Optional{inner}` is a type-level
  discriminator over the existing tag scheme.
- Never branch on a raw `.?` value. `if nil_opt.?:` must funnel through
  `rt_is_some`, or nil (=3) reads truthy — a silent wrong-branch bug, strictly
  worse than a loud crash.

**A naive blanket no-op rule is wrong** and would regress `.first()`, which is
genuinely optional and is separately mis-lowered (returns the boxed `v<<3` — 24
for element 3 — never unwrapped). `.first()` must be *typed* `Optional` so it
takes the unwrap path; the no-op arm must apply only to provably non-Optional
operands.

## Staged sequence (each stage builds and lands alone)

**Stage 0 — repair `rt_index_of`.** Steps 1-2 **LANDED 2026-07-28** by a third
lane, `5c75a1bbce0` *"fix(jit,runtime): register rt_index_of so index_of stops
de-JITting the module"*, which added the definition to `collections.rs` **and**
the registrations (`common/src/runtime_symbols.rs`, `codegen/runtime_sffi.rs`,
`codegen/jit.rs`) in one commit. Verified at `origin/main`: the definition is now
at `collections.rs:3051` and `rt_index_of` appears in both symbol tables. The
unpushed `0d864c55fe7` is no longer load-bearing for this symbol (though it may
still carry unrelated borrow-checker work worth landing).

**Correction to an earlier draft and to a peer's report: only TWO codegen sites
emit `rt_index_of`**, not four — `codegen/instr/calls.rs:3234` and
`codegen/instr/closures_structs.rs:1284`. Verified at `origin/main` by grepping
the emitted *symbol* rather than the method name. `llvm/emitter.rs:191` and
`llvm/functions.rs:2274` match on `"index_of"` but emit **`rt_string_find`**;
counting them as `rt_index_of` sites conflates the method name with the target.

Still open, and now the substance of Stage 0:

1. **Backend divergence — HYPOTHESISED, then REFUTED. Deprioritised.** An earlier
   revision of this plan predicted that `arr.index_of(x)` would silently yield
   `-1` under LLVM and the correct index under the JIT, and ranked it above the
   Optional work. **It does not reproduce.** A peer lane A/B'd it on a binary
   built from `b410e53a7a2`: the JIT lane is fully correct
   (`arr.index_of(30)`→`2`, `"hello world".index_of("world")`→`6`, miss→`-1`),
   and the LLVM/native lane does not silently disagree — it fails loudly with
   `MIR lowering error: unresolved method call: index_of`, rc=1, no binary
   emitted. A control probe without `index_of` builds clean.

   Two independent corroborations that this class is loud, not silent: the
   diagnostic originates in the **pure-Simple** compiler
   (`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:1881` and siblings) —
   *not* the Rust seed this plan concerns, so it is outside this workstream's
   scope entirely.

   **Withdrawn corroboration.** An earlier revision also cited
   `doc/08_tracking/bug/native_string_methods_unresolved_in_mir_2026-07-17.md` as
   independently confirming the family is loud. **That citation was wrong and is
   withdrawn.** That doc asserted a Task #145 guard "converting unresolved calls
   into hard errors rather than silently emitting a placeholder"; no such guard
   exists, and the doc has now been corrected (2026-07-28). Do not re-cite it for
   this purpose.

2. **Task #145 const-0 placeholder — the real silent-wrong-answer risk, OPEN.**
   At `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:2485-2500`,
   `self.error("unresolved method call: {method}", nil)` does **not** abort
   lowering — the const-0 placeholder is emitted immediately after. The in-source
   comment says why: `self.error` only *collects*, and both the bootstrap lane
   (`driver_bootstrap.spl` reads `ctx.errors`, never `MirLowering.errors`) and
   the native-build worker drop that list, so the placeholder "ships as SILENT
   data loss (exit 0, no stderr) — exactly how the `.join()` no-op survived
   undetected." The `print` WARNING exists *because* the error is not reliably
   fatal. **Fatality depends on the consumer of the error list, not on the
   guard.**

   Measured on `b410e53a7a2`: `native-build` default → 3 const-0 warnings, hard
   error surfaced, rc=1. `native-build` with `SIMPLE_BOOTSTRAP=1` → 3 warnings,
   **hard error not surfaced at all**.

   NOT yet demonstrated: end-to-end exit-0-with-a-wrong-value. The bootstrap run
   died pre-codegen for an unrelated reason. Mechanism confirmed, one
   error-swallowing lane confirmed, silent wrong answer not reproduced. To close
   it, find a lane reaching codegen with the error list dropped.

   This is the same failure shape as the nil-sentinel-3 defect this plan exists
   to fix — a placeholder value indistinguishable from real data — and it is the
   highest-value open item in Stage 0.
3. **`rt_string_index_of` is still unreachable.** At `origin/main` it appears
   only as a `RuntimeFuncSpec` registration (`runtime_sffi.rs:413`); no
   method-name dispatch selects it. It remains the only genuinely
   Option-returning implementation, so it is the natural target once `index_of`
   is retyped `Optional` in Stage 4 — but today it is dead code.

No type change is involved in either. Do NOT author a second `rt_index_of` and do
NOT delete the two call sites — it is the only receiver-polymorphic `index_of`,
and removing it forces every caller to choose array-vs-text statically, the
opposite of what the P5 divergence needs.

**Stage 1 — add the variant, unused.** Add `HirType::Optional{inner}`, fix the 3
`E0004` sites, register nothing to it. Oracle: `--emit-archive --target
x86_64-unknown-none` must produce **byte-identical archives**, proving a no-op.

**Stage 2 — type-level `??` rule.** `lower_coalesce` dispatches on static type as
above. Still no method retyped, so `Optional` is never produced — archives should
again be byte-identical. This is the stage that requires `control.rs` ownership.

**Stage 3 — retype `first`/`last`/`get`** (`mod.rs:1039`) to `Optional(element)`,
and fix their lowering to unwrap rather than return the boxed form. Smallest
genuinely-optional family; validates the whole mechanism.

**Stage 4 — migrate the `index_of` family** on top of Stage 0's now-consistent
runtime, receiver class at a time (string, then array), re-running the archive
oracle per class. Guard against the P6 BoxInt/static-dispatch regression at every
step.

**Stage 5 — audit the 18 `PointerKind::Shared` sites** for pointer-means-optional
and convert. Only then is the defect class dead.

Stages 0 and 1 are independently landable today. Do not claim the class is fixed
before Stage 5.

## Coordination

`control.rs` is owned by another lane landing the `.?`-to-BOOL/SIGILL stopgap
(value → `T?`, condition → `rt_is_some`, **bool-return → `rt_is_some`**; that
lane measured 42 owned `-> bool` functions returning a bare `.?`, ~10 inside
`src/compiler/`). Agreed sequencing: **stopgap first, this plan subsumes the
value-position half later.** The bool-return coercion should remain permanently —
it honours a declared return type and is not a `.?` workaround.

Mirror gap, read from source, not executed: the pure-Simple compiler has the same
hole at `src/compiler/50.mir/mir_lowering_stmts.spl:1333` (`lower_if` calls
`lower_expr(cond)` with no `ExistsCheck` case, so a bare `if opt.?:` branches on
the sentinel). `if val v = opt.?:` is safe — the parser desugars it.

Perf landmine for Stage 2: rewriting lowering paths can perturb the JIT extern
set and silently demote a module to the interpreter. Watch
`codegen_fallback_hits` and the JIT-fallback log line, not just correctness.

## Testing note

Do **not** write tests using `.?` inside `expect(...)`. On the spec/matcher path
`.?` yields the payload, not a bool, so `expect(x.?).to_equal(true)` always lies.
Use `match` or `.is_some()`.
