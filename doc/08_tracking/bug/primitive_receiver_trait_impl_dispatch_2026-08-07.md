# Trait `impl` blocks on PRIMITIVE Self types are honoured only by the interpreter

- **Status:** OPEN (diagnosed, root cause located, not fixed) — re-verified
  2026-08-07 (same day, follow-up probe), matrix unchanged.
  2026-08-08: the `use std.hash` export half is FIXED (30697f688ed,
  b73597bfd03). Defect A (seed JIT) still unfixed. Defect B now has a
  MEASURED fix recipe (see "Defect B fix recipe" below) that reached
  0 `unresolved method call` on the native-min repro but was lost to a
  concurrent-session working-copy clobber before it could be landed.
  2026-08-09: a registration-key fix for Defect B's two gaps (legacy-map
  registration + resolver fall-through) is applied in `.spl` source (see
  "Edit 1 + registration-gap fix LANDED, 2026-08-09" below) but is
  **UNVERIFIED BY EXECUTION** — the same vacuity blocker documented under
  "Verification loop is VACUOUS" recurs: the deployed `bin/simple` is the
  Rust seed and does not execute edited `src/compiler/**/*.spl` source at
  all (confirmed fresh with a liveness-marker eprint, 0 hits, both via
  `bin/simple test` and `SIMPLE_EXECUTION_MODE=interpret bin/simple run`).
  Observing this class of fix requires a bootstrap rebuild, which this
  lane was instructed not to run. Defect A remains unfixed and out of
  scope (`src/compiler_rust/**` is off-limits to this lane). Not one
  unified fix: Defect A (seed) and Defect B (pure-Simple resolver) are two
  independent code bases with independent root causes that merely share
  the same *shape* ("primitives carry no symbol, so anything keyed on
  symbol treats them as impl-less").
- **Date:** 2026-08-07
- **Spec (RED by design, locks in the interpret column):**
  `test/01_unit/language/primitive_receiver_trait_impl_dispatch_spec.spl` —
  `bin/simple test` on this file: `Results: 7 total, 6 passed, 1 failed`, the
  one failure being the i32-collapses-to-i64-impl row (asserts the correct
  1003, measures 1002). Do not weaken that assertion; it documents this bug.
- **Severity:** high — one variant fails **open** (silently wrong), one **SIGSEGVs**
- **Repro (committed):**
  - `test/fixtures/repro/compiler/primitive_trait_impl_dispatch_repro.spl` (interpret + JIT)
  - `test/fixtures/repro/compiler/primitive_trait_impl_dispatch_native_min.spl` (native MIR)
- **Sites:**
  - `src/compiler/35.semantics/resolve_strategies.spl:140-168` (`try_trait_method`)
  - `src/compiler/35.semantics/resolve.spl:89-93` (`get_type_symbol`)
  - `src/compiler/20.hir/hir_lowering/_Items/trait_impl_lowering.spl:242-244` (registration)
  - `src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs:1530` (seed JIT builtin shadow)

## Origin: a sibling lane's claim, reproduced but MISDIAGNOSED

A sibling lane reported that a `return 424242` sabotage inserted into
`impl Hash for f32` in `src/lib/nogc_sync_mut/src/hash.spl` was **invisible**, and
concluded "trait dispatch on primitive FLOAT types does not reach user impls,
while `text.hash()` correctly reached hash.spl".

Both halves of that conclusion are wrong, and the real defect is bigger.

Paired-sentinel run (all six impls sabotaged with distinct values in one edit),
`bin/simple run`, `use std.nogc_sync_mut.src.hash`:

| impl | sentinel | INTERPRET | JIT |
|------|----------|-----------|-----|
| `text` | 424241 | **424241 visible** | 177693 — sentinel INVISIBLE |
| `i64`  | 424243 | **424243 visible** | 0 — INVISIBLE |
| `i32`  | 424246 | 424243 — reaches the **i64** impl | 0 — INVISIBLE |
| `bool` | 424244 | **424244 visible** | 0 — INVISIBLE |
| `f32`  | 424242 | **424242 visible** | 0 — INVISIBLE |
| `f64`  | 424245 | **424245 visible** | 0 — INVISIBLE |

So:

1. It is **not float-specific.** Under JIT *every* primitive impl is bypassed.
2. `text.hash()` does **not** reach `hash.spl` under JIT either. `177693` is the
   seed runtime's own `rt_hash_text`, not `hash.spl`'s FNV-1a (`-5808529385363204345`).
   The sibling's control was itself false-green.
3. Under the interpreter the f32 sabotage **is** visible — the original claim
   does not reproduce there at all.

## Two DISTINCT defects, different failure modes

### Defect A — seed JIT builtin-name shadow (fails **OPEN**, silent)

`src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs:1530`

```rust
"hash" => "rt_hash_text",
```

is matched on the method NAME with no receiver-type gate. Every `.hash()` call
in JIT-compiled code is rewritten to `rt_hash_text(receiver)` regardless of what
the receiver is and regardless of any user `impl Hash for T`:

- numeric / bool receiver → the raw scalar is passed as a text pointer → **0**
- text / char receiver → the runtime's hash, **not** the user impl's

This is what made the sabotage invisible. It is the dangerous variant: no error,
no warning, rc=0.

Contrast: a method name that is NOT in that builtin table fails closed —
`Runtime error: Function 'str.marker_probe' not found ... Refusing to substitute
a placeholder value`. So the silent-wrongness is exactly the intersection of
"user impl on a primitive" with "name collides with a seed builtin". Other names
in the same table (`len`, `push`, `pop`, `contains`, `at`, `unwrap`, …) are the
rest of the blast radius.

### Defect B — pure-Simple: primitive Self types are not symbol-bearing (fails **CLOSED**)

`src/compiler/35.semantics/resolve.spl:89`

```
static fn get_type_symbol(ty: HirType) -> SymbolId?:
    match ty.kind:
        case Named(sym, _): sym
        case _: nil
```

Primitive HIR types are `HirTypeKind.F32` / `I64` / `Str` / `Bool` / … — never
`Named` — so `get_type_symbol` returns nil for all of them. `try_trait_method`
(`resolve_strategies.spl:148-153`) then bails **before** it can reach the
`TraitSolver` fallback:

```
if val found_type_id = TypeChecker.get_type_symbol(receiver_type):
    type_id = found_type_id
if not type_id.is_valid():
    return nil            # <-- primitives die here, solver never consulted
```

`try_trait_method_with_solver` — which matches structurally via
`TraitSolver.find_impl` / `ImplBlock.matches_type` and could handle a primitive
— is unreachable for any primitive receiver.

Registration has the matching hole. `20.hir/hir_lowering/_Items/trait_impl_lowering.spl:242`:

```
val concrete_symbol_name = match type_.kind:
    case Named(owner_symbol, _): self.symbols.method_symbol_name(owner_symbol, default_fn.name)
    case _: default_fn.name
```

A primitive impl registers its method under the **bare, unqualified** name. Every
`impl Trait for <primitive>` in a module therefore competes for one key — which
is exactly the observed `i8`/`i16`/`i32` → `i64`-impl collapse below.

Consequence under native: `MIR lowering error: unresolved method call: <method>`
for both `text` and `f32` receivers. Loud, fails closed — a defect, but not a
silent one.

## Dispatch matrix (measured, `bin/simple`, 2026-08-07)

Custom trait `MarkerProbe`, same-module impls, non-builtin method name:

| receiver | interpret | JIT | native-build |
|----------|-----------|-----|--------------|
| `struct` (control) | correct | correct | correct |
| `text` | correct | hard error | `unresolved method call` (measured) |
| `i64`  | correct | hard error | not measured |
| `i32`  | **reaches i64 impl** | hard error | not measured |
| `bool` | correct | hard error | not measured |
| `f32`  | correct | hard error | `unresolved method call` (measured) |
| `f64`  | correct | hard error | not measured |

The struct control passing in all three engines is what proves this is specific
to primitive Self types, not to trait dispatch generally.

**Measurement caveat for the native column.** The `native-build` results were
measured on the minimal two-impl file
(`primitive_trait_impl_dispatch_native_min.spl`), which yields exactly
`unresolved method call: mark` x2 — one per primitive receiver. The larger
`_repro.spl` cannot be used for the native column: its build fails first on
unrelated pre-existing prelude errors (`unresolved method call: merge`,
`unsupported MIR type kind [infer-arm]`), which mask this signal. That is why the
two files are committed separately.

`std.hash` (`impl Hash for …`, builtin-shadowed name), interpret column, against
the impl bodies actually written in `hash.spl`:

| receiver | measured | expected from hash.spl | verdict |
|----------|----------|------------------------|---------|
| `text` | -5808529385363204345 | FNV-1a | correct |
| `i64` / `bool` / `f32` / `f64` | 7 / 1 / -1048551023779512320 / 8620509230693463792 | matches the impl bodies | correct |
| `i8`, `i16`, `i32` | 7 | `self * FNV_PRIME` (i8/i16), `self as i64` (i32) | **WRONG — collapses to the `i64` impl** |
| `u8`, `u16`, `u32`, `u64` | `method 'hash' not found on type 'u8'` | the impls exist in hash.spl | **impls unreachable** |

The unsigned row is a third distinct finding: `impl Hash for u8` … `u64` are
written in `hash.spl` and are dead even under the interpreter.

## Item 2 — `hash_of<T: Hash>` SIGSEGV: same family, worse symptom

```
fn hash_of<T>(x: T) -> i64 where T: Hash:
    x.hash()
```

`bin/simple run` → **rc=139 (SIGSEGV, core dumped)**, for a `text`, `f32` *and*
`i64` argument. Under `SIMPLE_EXECUTION_MODE=interpret` the identical file
returns correct values (rc=0).

It is not `Hash`-specific and not `hash`-specific: the same shape with a custom
trait and a custom method name segfaults identically. Substituting a **struct**
receiver through the same generic bound returns the correct value under JIT.

So the boundary is exactly the same as Defect B — generic trait-bound dispatch to
a **primitive** receiver — but the JIT's failure there is a segfault rather than
a refusal.

## What is NOT affected (checked, so the severity is not overstated)

Built-in `Dict<i64, i64>` insert/lookup is **correct in both engines** (3/3).
The all-zero JIT hash does not corrupt or collapse the built-in dict — it does not
route through the `Hash` trait. The damage is confined to explicit `.hash()`
call sites and to anything layered on `std.hash` directly.

## Also found while probing

`use std.hash` does not resolve the trait or the impls at all —
`Module "std.hash" does not export 'Hash'` (the trait is declared without `pub`),
and plain `use std.hash` leaves `.hash()` unresolved on every receiver. Only
`use std.nogc_sync_mut.src.hash` works. `src/lib/nogc_sync_mut/src/map.spl:5`
uses the non-working `use std.hash.Hash` form; an unresolved `use` is only a
warning, so that import is silently inert.

## Unresolved axis — CLOSED 2026-08-07 (follow-up attempt)

Whether the `i32`/`i8`/`i16` → `i64` collapse is "the `as` cast does not retype
the value" or "dispatch discards the integer width" is now settled: it is
**dispatch keying, not cast retyping**. Probe (`SIMPLE_EXECUTION_MODE=interpret
bin/simple run`, no `as` anywhere):

```
trait MarkerProbe: fn marker_probe() -> i64
impl MarkerProbe for i64: fn marker_probe() -> i64: 1002
impl MarkerProbe for i32: fn marker_probe() -> i64: 1003

val v: i32 = 7
v.marker_probe()             # -> 1002 (want 1003)

fn take_i32(x: i32) -> i64: x.marker_probe()
take_i32(9)                  # -> 1002 (want 1003)
```

Both a `val: i32` and an `i32` function parameter — no cast in sight — still
collapse to the `i64` impl. This rules out "the `as` cast doesn't retype the
value" entirely; whatever collides, it collides on the receiver's static type
identity itself, not on cast handling.

## `trait_impl_lowering.spl:242-244` attribution WITHDRAWN 2026-08-07

That site is dead code for every case this bug doc measures, for two
independent reasons:

1. `if not methods.contains_key(default_fn.name):` at line 239 gates the
   block — it only fires for trait **default** methods an impl does NOT
   override. Every impl in the repro fixture and in `hash.spl` explicitly
   defines its method, so this guard is always false for them.
2. `trait MarkerProbe: fn marker_probe() -> i64` and `hash.spl:37 fn hash() ->
   i64` are both **bodyless required methods** (no default body), so
   `trait_hir.defaults` is empty for both traits and the
   `for default_fn in trait_hir.defaults:` loop never iterates at all.

So the bare-name registration at line 244 cannot be the mechanism behind the
measured i32→i64 collapse for either the `MarkerProbe` repro or `std.hash`.
The real collision site is somewhere in primitive-receiver method dispatch
proper — plausibly still a bare/normalized-name keying collision, but not at
this call site. Not re-diagnosed in this lane (see next section for why).

## Verification loop is VACUOUS for this defect — attempt STOPPED 2026-08-07

A follow-up lane attempted the registration-key fix (scoped tightly, per
instruction) and got as far as re-diagnosis before hitting a hard blocker:

**`bin/simple test <spec>` does not execute edited `src/compiler/**/*.spl`
source for this spec, as of 2026-08-07.** Proven by liveness probe, not
assumed: an unconditional `eprint("LIVENESS_PROBE_MARKER...")` inserted as the
first statement of `lower_impl` in `trait_impl_lowering.spl` (guaranteed on
the path for any file with `impl` blocks, which both the fixture and every
provided spec have) produced **zero** occurrences of the marker across two
independent runs of
`bin/simple test test/01_unit/language/primitive_receiver_trait_impl_dispatch_spec.spl`,
while `Results: 7 total, 6 passed, 1 failed` stayed byte-for-byte identical
to the unedited baseline both times. The edit was reverted after each probe
(`git diff --stat` on the file returns clean / marker count 0 post-revert).

This directly **contradicts**
`.claude/memory/reference_compiler_spl_edits_are_live_under_bin_simple_test.md`
(dated 2026-08-06, one day prior), which claims `.spl` compiler edits are live
under `bin/simple test` via the seed's interpreter loading source directly.
Something changed between that observation and today, or the two lanes hit a
different code path (that memory's proof point was
`src/compiler/50.mir/mir_lowering_stmts.spl`, a MIR-lowering file, not this
HIR-lowering file). The test log's own `child binary:
/home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple`
line, combined with that binary's own `--version` banner ("this Rust-built
Simple binary is a bootstrap seed only"), corroborates but does not by itself
prove seed-only execution — per
`.claude/memory/reference_positive_capability_probe_for_binary_identity.md`,
banners can lie. The load-bearing fact is the marker probe, not the banner.

**Consequence:** no edit to `src/compiler/**/*.spl` in this area can be
verified against the one usable oracle
(`primitive_receiver_trait_impl_dispatch_spec.spl`, interpreter lane) in this
environment right now. Per this lane's own instructions, a change that cannot
be verified is not to be shipped. No fix was attempted or landed. This is a
harness-level blocker on top of the original one (bootstrap stage 3 blocked,
no self-hosted binary) — both must be resolved before this defect is
fixable-and-verifiable in one lane.

**A/B control attempted, 2026-08-07 — INCONCLUSIVE, do not over-read.** A
follow-up probe placed the same unconditional `eprint` at
`src/compiler/50.mir/mir_lowering_stmts.spl:49` (`mir_hir_type_is_isolated`)
— the exact site
`.claude/memory/reference_compiler_spl_edits_are_live_under_bin_simple_test.md`
cites as PROVEN live on 2026-08-06 — and ran it against
`test/01_unit/compiler/borrow/iso_move_pipeline_spec.spl` (the same spec that
memory used). That run produced no `Results:` line at all (`ERROR: test
daemon timed out`). Critically, a **re-run of the unedited baseline for the
*same* spec afterward also timed out with no `Results:` line**, and a
subsequent re-run of `primitive_receiver_trait_impl_dispatch_spec.spl` itself
(the spec used for the original, successful probes) — both unedited and with
a third probe edit in `resolve.spl:89` (`get_type_symbol`) — likewise timed
out, even after `test_daemon_stop`. So the test daemon/environment degraded
mid-session (consistent with `.claude/memory/reference_...` notes on box load
causing spec timeouts that are "not a RED"), and **none of these three later
runs are usable evidence either way** — a timed-out run with no verdict
cannot confirm or refute liveness. All three probe edits from this batch were
reverted (`git diff --stat` per file, `grep -c LIVENESS_PROBE` = 0, on
`mir_lowering_stmts.spl` and `resolve.spl` both, post-revert).

**What still stands, scoped correctly:** the original vacuity finding is
based on the *first* three runs in this lane (baseline, `self.error` probe,
`eprint` probe — see above), which all completed cleanly within ~180s with
byte-consistent `Results: 7 total, 6 passed, 1 failed` and zero marker
occurrences, run *before* the environment degraded. That is real evidence
that an edit to `trait_impl_lowering.spl:157` (`lower_impl`, first statement)
was not observed while compiling
`primitive_receiver_trait_impl_dispatch_spec.spl` at that time. It is **not**
confirmed as a universal, harness-wide, or still-current fact — the broader
claim ("no `.spl` edit is ever live") is withdrawn as unverified; a future
lane should re-run the A/B control in a quiet environment before relying on
it.

## ROOT CAUSE LOCATED — 2026-08-07, and it is OUT OF SCOPE for this repo

A parallel research pass (independent of the verification-loop finding above,
launched before it landed) traced the actual i32→i64 collapse mechanism all
the way to source, using `SIMPLE_EXECUTION_MODE=interpret` against the
deployed `bin/simple` (confirmed Rust seed, per the `--version` banner and
`git log` on `bin/release/x86_64-unknown-linux-gnu/simple`). The mechanism is
entirely inside `src/compiler_rust/`, not in `src/compiler/**/*.spl` at all —
which also explains why the doc's original citation of a `.spl`-side
registration key was never going to be the fix, independent of the
verification blocker above.

**Registration is correct — impls do NOT collide.**
`src/compiler_rust/compiler/src/interpreter_eval.rs:1064-1070` (module scope)
and `src/compiler_rust/compiler/src/interpreter_call/block_execution.rs:909-912`
(block/closure scope) register each `impl Trait for T` into
`TRAIT_IMPLS: HashMap<(String, String), Vec<Arc<FunctionDef>>>` keyed
`(trait_name, impl_type_name)` (`interpreter_state.rs:249`), where
`impl_type_name` comes from `get_type_name` (`interpreter_types.rs:22-32`),
which clones the parsed type name verbatim for `Type::Simple(name)`. So
`impl MarkerProbe for i32` and `impl MarkerProbe for i64` land under the
genuinely distinct keys `("MarkerProbe","i32")` and `("MarkerProbe","i64")`.

**The lookup is where the collision happens.** Both
`src/compiler_rust/compiler/src/interpreter_method/mod.rs:1430-1463` and a
duplicated copy for chained calls at
`src/compiler_rust/compiler/src/interpreter_helpers/method_dispatch.rs:747-762`
fall back, when a type-specific handler doesn't recognize the method, to a
**fixed candidate-name list keyed on the receiver's runtime `Value` variant**,
not its declared/static type:

```rust
let type_names: &[&str] = match &recv_val {
    Value::Str(_) => &["text", "str", "String"],
    Value::Int(_) => &["i64", "i32", "int"],
    ...
};
for type_alias in type_names {
    for ((_trait_name, impl_type), methods) in trait_impls.iter() {
        if impl_type == type_alias { /* return FIRST match */ }
```

`Value::Int` is the single runtime representation for **every** integer
width in this interpreter — i8/i16/i32/i64 are indistinguishable at this
point. So an i32 receiver (or i8/i16) walks the *same* candidate list
`["i64","i32","int"]` as a genuine i64 receiver, `"i64"` is tried first, and
since an `impl ... for i64` almost always exists it wins before `"i32"` is
ever reached — reproducing the exact collapse this doc documents. u8/u16/u32/u64
aren't in the candidate list at all, independently explaining why this doc's
matrix reports those as unreachable ("method not found") rather than
colliding with i64 — same mechanism, different outcome depending on whether
the receiver's width happens to be in the hardcoded list.

**This is squarely inside the disposable Rust seed
(`src/compiler_rust/`).** The seed is sanctioned bootstrap infrastructure, not
the deliverable, and lanes working this bug have been instructed not to edit
it (a task-scope constraint, not a repo-wide prohibition — the seed itself is
legitimate Rust code by design). Combined with the verification-loop
finding above (edited `.spl` source is not observably live today), this
defect currently has **no compliant, verifiable fix path** in this
environment: the correct-looking `.spl`-side fix cannot be verified, and the
only mechanism actually proven to cause the measured symptom lives in code
this repo's own rules place off-limits.

Filed, not fixed. Recommended next step for a future lane: (1) resolve why
`.spl` compiler edits are not observably live under `bin/simple test` as of
2026-08-07 (candidate separate bug — see A/B control above), which is a
prerequisite for verifying *any* `.spl`-side compiler fix, not just this one;
(2) once verifiable, decide whether the seed's ordered-fallback dispatch
(`interpreter_method/mod.rs:1430-1463`,
`interpreter_helpers/method_dispatch.rs:747-762`) needs a matching Rust-side
fix regardless (since the deployed tool today runs the seed, not any
self-hosted binary), which would need explicit user sign-off to touch the
seed.

## Suggested fix (still not attempted — compounded reasons)

The original two-part suggestion (key primitive impl registration on the
primitive's type kind rather than a bare name; let `try_trait_method` fall
through to `try_trait_method_with_solver` instead of returning nil when the
receiver type carries no symbol) may still be directionally right, but its
proposed landing site (`trait_impl_lowering.spl:242-244`) is now known wrong
(see above) and the actual collision site was not re-located in this lane —
the re-diagnosis effort was abandoned once the verification loop proved
vacuous, to avoid spending budget locating a site for an unverifiable change.

Two blockers now stack: (1) `try_trait_method` is hot-path code in a compiler
with no self-hosted binary (bootstrap stage 3 blocked), and (2) even the one
available oracle (`bin/simple test` on the interpreter lane) does not execute
edited `src/compiler/**/*.spl` source as of 2026-08-07. Until (2) is resolved
(establish which binary/path `bin/simple test` actually runs specs through,
and how to make a `.spl` source edit observable there again), any edit to this
area is unverifiable by construction and should not be attempted.

Defect A is a one-arm change in the disposable Rust seed (gate `"hash"` on the
receiver's static type, or drop the arm so it fails closed like every other
un-implemented primitive method). Filed rather than applied because the seed is
explicitly not the deliverable — but note that until it is fixed, **every
`.hash()` call on a primitive in JIT-compiled code silently returns 0**.

## Defect B fix recipe — MEASURED to remove `unresolved method call`, NOT LANDED (2026-08-08)

A fix lane built and traced this end-to-end on the native-min repro. The
resolver fall-through alone is **not** sufficient; four coordinated edits were
needed, and the trace below is the evidence for each. **The working tree
carrying these edits was reverted by a concurrent session before it could be
landed — the code is gone, this recipe is what survives.** Re-apply and re-verify
before trusting it.

1. `35.semantics/resolve_strategies.spl` `try_trait_method`: when
   `get_type_symbol` yields no valid symbol, `return
   self.try_trait_method_with_solver(receiver_type, method)` instead of `nil`.
2. Same file, `try_trait_method_with_solver`: its success path constructed
   `MethodResolution(trait_name:…, impl_block:…, method_name:…, is_generic:…)`
   — a **field-bag that does not match the enum** in `hir_types.spl:129`. MIR
   lowering can only consume the variant, so build
   `MethodResolution.TraitMethod(trait_name.id, method_sym)` via
   `lookup_trait_method_raw`. This is a second latent defect, independent of
   primitives: *every* solver-resolved trait method was returning an
   unconsumable resolution.
3. Primitive impls carry no type symbol, so `50.mir` keys them on a canonical
   name. Add `hir_primitive_impl_owner_name(kind) -> text` to
   `mir_lowering_types.spl` (`Int(bits,signed)` → `i{bits}`/`u{bits}`,
   `Float(bits)` → `f{bits}`, `Bool`/`Char`/`Str` → `bool`/`char`/`text`, else
   `""`); register under it in `_MirLowering/module_lowering.spl`'s impl loop
   (the `case _:` arm of the `impl_def.type_.kind` match, which previously left
   `impl_type_name` empty and skipped registration entirely); and add a
   primitive-owner recovery block in `_MirLoweringExpr/method_calls_literals.spl`'s
   `case Unresolved:` arm, placed AFTER struct-owner recovery and BEFORE the
   builtin `push`/`char_code_at`/`to_text` special cases.
4. Receiver-type recovery needs three sources, in this order: `receiver.type_`,
   then `receiver_declared_type(receiver)`, then — for `(1.5 as f32).mark()` —
   the **cast target** from `case Cast(_, target)`. With only the first two the
   trace printed `prim-owner method=mark owner=` (empty) and the f32 row still
   failed; adding the cast arm produced `owner=f32`.

Measured progression on
`test/fixtures/repro/compiler/primitive_trait_impl_dispatch_native_min.spl`:

| state | `unresolved method call: mark` |
|-------|-------------------------------|
| origin/main | 2 (f32 + text) |
| after edits 1+2 only | 2 — solver reached, resolution unconsumable |
| after edits 1+2+3 | 1 (text resolved: `prim-key key=text::mark found=true`) |
| after edits 1+2+3+4 | **0** — both `f32::mark` and `text::mark` found |

**Residual, unfixed:** the build still fails, now on a *different* and
pre-existing error — `unsupported MIR type kind [infer-arm]:
HirTypeKind::Infer((0,0))` at the repro's line 25 col 40. Impl-method symbols on
the flat lane can carry an unresolved `Infer` return type, and
`resolved_call_return_type` → `lower_type` treats `Infer` as fatal. Guarding the
primitive call site (default `i64`, `bootstrap_text_type()` for `Str`) removed
the primitive-path instances but a third remains from elsewhere. So Defect B's
*dispatch* half is solved by the recipe above; the native build of this fixture
is still blocked by the infer-arm defect, which deserves its own entry.

**Verification gap.** No self-hosted binary exists (stage 3 blocked), so this was
verified only by MIR-lowering trace on the toy fixture. A resolver-level unit
spec calling `try_trait_method` with primitive `HirType`s was written and also
lost in the same clobber.

## Reproduce

```
bin/simple run test/fixtures/repro/compiler/primitive_trait_impl_dispatch_repro.spl
SIMPLE_EXECUTION_MODE=interpret bin/simple run test/fixtures/repro/compiler/primitive_trait_impl_dispatch_repro.spl
bin/simple native-build test/fixtures/repro/compiler/primitive_trait_impl_dispatch_native_min.spl -o /tmp/x
```

Interpret prints `FAILURES=1` (the `i32` row) — the `struct(control)`, `text`,
`i64`, `bool`, `f32` and `f64` rows all PASS, which is the non-vacuity proof for
this probe. JIT prints `PASS struct(control) = 5001` and then stops at the first
primitive receiver with `Runtime error: Function 'str.marker_probe' not found`
(rc=70). The native file reports `MIR lowering error: unresolved method call:
mark` twice (rc=1) — once per primitive impl — while the same file runs correctly
under interpret (`f32 = 1006`, `text = 1001`).

## Recipe re-application attempt, 2026-08-08 — edit 2 LANDED, edits 1/3/4 BLOCKED

A follow-up lane re-applied the recipe from a **detached worktree pinned to
`origin/main`** (the shared working copy was carrying 23 unrelated in-flight
compiler edits from parallel sessions, including `expr_dispatch.spl` +86 —
measuring there would have been measuring someone else's tree).

### Edit 2 landed: `af3ad25e761e412325a1e8802fa42407d2b6d960`

`try_trait_method_with_solver` now returns
`MethodResolution.TraitMethod(trait_name.id, method_sym)` via
`lookup_trait_method_raw`, instead of the
`MethodResolution(trait_name:, impl_block:, method_name:, is_generic:)` field
bag. Confirmed against the enum at `20.hir/hir_types.spl:129`: its only shapes
are `InstanceMethod` / `TraitMethod` / `FreeFunction` / `StaticMethod` /
`Unresolved`. No struct form exists, so the old value was unmatched by every
consumer.

### CORRECTION to this doc's blast-radius claim — it is LATENT, not active

This doc previously said the field bag meant "**every** solver-resolved trait
method was returning an unconsumable resolution". That overstates it. Measured:

- The only resolver entry point wired into the driver is `resolve_methods`
  (`80.driver/driver_hir_pipeline_lowering.spl:220`,
  `driver_hir_pipeline_passes.spl:30`).
- It builds its resolver via `create_method_resolver` →
  `create_trait_solver_for_resolution` (`35.semantics/resolve.spl:148`), a
  `TraitSolver` constructed with **every map empty** — `traits: {}`,
  `impls: {}`, `impls_by_type: {}` — and never populated afterwards.
- `try_trait_method_with_solver` is gated by
  `if self.trait_solver.trait_methods.has(method)`, which on an empty dict is
  always false. The malformed construction was therefore **never executed**.
- The one entry point that could supply a populated solver,
  `resolve_methods_with_solver` (`resolve.spl:812`), is a **stub**: it returns
  `(module, [])` and ignores the solver entirely.

Probes at (A) solver entry, (B) the solver success path, and (C) the
no-symbol bail in `try_trait_method` recorded **0 hits each**, on both the
primitive fixture and a struct-receiver control.

So the correct statement is: the solver-resolved set is currently **empty**;
the field bag was a landmine in unreachable code, standing directly in front of
any work that populates the solver. Fixing it is a prerequisite for recipe edit
1, not a fix for an observable miscompile today.

This also explains the recipe's own row "after edits 1+2 only → 2, no change":
edit 1 falls through to a solver that has nothing registered in it, so it
returns nil regardless.

### Edits 1, 3, 4 NOT landed — the oracle no longer exists

`bin/simple native-build` is **broken for every input** at `origin/main` as of
2026-08-08, including a two-line hello-world. The recipe's RED signal
(`unresolved method call: mark` ×2) cannot be reproduced, so neither RED nor
GREEN is obtainable for the dispatch half. Filed separately:
`doc/08_tracking/bug/native_build_nil_deref_total_outage_2026-08-08.md`.

### Measurement trap that affects this doc's own numbers

`native-build` truncates the **middle** of stderr (`OUTPUT_LIMIT = 12000` in
`src/app/cli/native_build_main.spl:61`; head 6000 + tail 6000). Compiler
diagnostics land in the discarded middle, so `grep -c` over native-build output
is **fail-open** — 0 can mean "truncated", not "absent". The counts in this
doc's recipe table were taken through that truncation and should be re-measured
with the limit raised before being trusted.

## Edit 1 + registration-gap fix LANDED, 2026-08-09 — unverifiable by execution, verified by trace

Re-verified fresh at `origin/main` `c97ae6cf426c` (2026-08-09). `native-build`
is still unusable: both the native-min repro and a trivial hello-world time out
(>90s, no output) rather than the fast nil-deref this doc previously recorded —
same practical outcome (no oracle), worse symptom. Not re-filed separately;
consistent with `native_build_nil_deref_total_outage_2026-08-08.md`.

**Root cause refinement.** Edit 1 alone (the `try_trait_method` fall-through)
is confirmed correct but was previously assumed sufficient once combined with
edit 2 (already landed, `af3ad25e761e`). It is not: `build_trait_impls`
(`resolve.spl:235-259`), which populates the **legacy** `trait_impls: Dict<i64,
[SymbolId]>` map that `try_trait_method` checks first, silently drops every
`impl Trait for <primitive>` via its `case nil: pass` arm — the same
"primitives have no SymbolId" hole as `get_type_symbol`, one level up. This is
why the struct control passes today (structs get a real symbol and reach the
legacy map) while primitives previously had **no reachable registration at
all**, independent of the TraitSolver being empty (confirmed still empty/inert
per the 2026-08-08 CORRECTION above — not touched by this fix, out of scope).

**Fix landed** (both in `resolve.spl`, same class):
1. `TypeChecker.primitive_type_key(kind: HirTypeKind) -> i64?` — a stable
   synthetic key per `(Int bits/signed, Float bits, Bool, Char, Str, Unit)`,
   disjoint from real `SymbolId`s (all `< -1000`, never collides with `i32`
   vs `i64` etc).
2. `build_trait_impls`: on `get_type_symbol(impl_.type_) == nil`, register
   under `primitive_type_key` instead of dropping the impl.
3. `try_trait_method` (`resolve_strategies.spl:148-163`): on
   `not type_id.is_valid()`, look up `primitive_type_key(receiver_type.kind)`
   in `self.trait_impls` before falling through to
   `try_trait_method_with_solver` (recipe edit 1), instead of the previous
   unconditional `return nil`.

Both changes are strictly additive — they only fire on the branch that
previously always returned `nil`/dropped the impl, so no previously-working
(struct/symbol-bearing) resolution path changes.

**Verification.** `bin/simple lint` on both edited files: clean (no errors,
only pre-existing unrelated warnings). Liveness-marker proof (unconditional
`eprint` as the first statement of `try_trait_method`, per this doc's own
methodology above): **0 hits** across `bin/simple test
test/01_unit/language/primitive_receiver_trait_impl_dispatch_spec.spl`
(`Results: 7 total, 6 passed, 1 failed` — byte-identical to the documented
baseline, marker reverted after the probe). This is expected, not vacuous: the
marker being 0 shows `MethodResolver.try_trait_method`
(`src/compiler/35.semantics/`) is **not on the interpret execution path** —
`bin/simple test`'s default interpret mode dispatches methods entirely inside
`src/compiler_rust/` (Defect A's engine: `TRAIT_IMPLS` HashMap +
`interpreter_method/mod.rs`), never loading this self-hosted resolver at all.
This resolver is wired only into `resolve_methods`
(`80.driver/driver_hir_pipeline_lowering.spl:282`,
`driver_hir_pipeline_passes.spl:30`), which is reached by the self-hosted
compiler pipeline (native-build / AOT), not by the seed interpreter. Since
native-build hangs/is unusable and no self-hosted binary exists (stage 3
blocked), this fix has **no execution oracle** in this environment right now —
same conclusion the 2026-08-08 update reached for edits 1/3/4, now confirmed to
also apply to the registration-gap half. The fix is correct by code trace
(traced the exact same way the doc traced Defect A into `compiler_rust`) but
not confirmed by a passing/failing test.

**Regression check.** The unaffected `primitive_receiver_trait_impl_dispatch_spec.spl`
baseline (6/7, interpret-mode) is unchanged, as expected since interpret
doesn't touch this code. No other trait-dispatch spec exists under
`test/01_unit/language/` to cross-check against (searched
`^trait |impl.*for.*:` — only this one file matches). Did not extend the spec
file further: any new assertion would hit the same unreachable-under-interpret
wall and add no real coverage without a working native-build/self-hosted
oracle.

**Status:** Defect A — confirmed still present, confirmed still out of scope
(`src/compiler_rust/`, editing forbidden). Defect B — the two gaps (resolver
fall-through + legacy-map registration) are now fixed in `.spl` source but
unverified by execution; MIR-lowering recipe edits 3/4 remain unapplied and
blocked on the same broken/hanging `native-build`. Not "one unified fix": the
seed (Defect A) and the pure-Simple resolver (Defect B) are two independent
code bases with two independent root causes (Rust ordered-fallback dispatch on
runtime `Value` variant vs. `.spl` symbol-keyed registration dropping
primitives) that happen to share the same *shape* of bug ("primitives have no
symbol, so anything keyed on symbol silently treats them as impl-less") but
require separate fixes in separate languages; only the pure-Simple side was
touched here, per scope.

---

## 2026-08-17 — CONTENT-BASED re-verification + first cross-engine RUN evidence

Verified by reading current source, not by commit SHA (SHAs are rewritten
constantly in this tree and prove nothing). Binary identity for every number
below: `readlink -f bin/simple` ->
`/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`;
`bin/simple --version` prints the seed banner, i.e. **everything measured here
is the Rust bootstrap SEED**.

### Which halves are live, by content

| half | site | state today |
|---|---|---|
| export half (`use std.hash`) | `src/lib/nogc_sync_mut/src/hash.spl` | already fixed (not re-probed here) |
| Defect B — resolver fall-through | `src/compiler/35.semantics/resolve_strategies.spl:158` | **fix PRESENT by content** (`primitive_type_key` consulted before bailing) |
| Defect B — registration key | `src/compiler/35.semantics/resolve.spl:95` (`primitive_type_key`, distinct per kind/bits/signedness) + `resolve.spl:282` (registers primitives under it) | **fix PRESENT by content** |
| Defect B — trait-DEFAULT-method registration | `src/compiler/20.hir/hir_lowering/_Items/trait_impl_lowering.spl:249-251` — still `case _: default_fn.name` (bare unqualified name) | **UNFIXED** |
| Defect A — seed JIT builtin-name shadow | `src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs:1790` — still literally `"hash" => "rt_hash_text"`, matched on method NAME with **no receiver-type gate** | **LIVE, unchanged** |

The Defect B fixes in `35.semantics` remain **unobservable through `bin/simple`**:
that binary is the Rust seed, whose own interpreter emits the diagnostics seen
below (`src/compiler_rust/compiler/src/interpreter/error_macros.rs:82`,
`interpreter/expr/calls.rs:615`). Edited `src/compiler/**/*.spl` is not executed
by it. Confirming that half still requires a bootstrap rebuild.

### RUN evidence (new — first time both engines were exercised)

Probe added: `test/01_unit/language/probe_primitive_receiver_trait_impl_dispatch.spl`
(text / i64 / i32 / u64 / bool / f32 / f64 receivers + a struct control; every
oracle an absolute literal). Exit status read on the line AFTER the command,
never through a pipe.

```
SIMPLE_RUST_SEED_WARNING=0 SIMPLE_TIMEOUT_SECONDS=600 SIMPLE_EXECUTION_MODE=interpreter \
  nice -n 19 bin/simple run test/01_unit/language/probe_primitive_receiver_trait_impl_dispatch.spl
rc=1
PRIMITIVE_TRAIT_IMPL_DISPATCH PROBE: begin
PASS text_receiver
PASS i64_receiver
PASS bool_receiver
PASS f64_receiver
FAIL i32_receiver expected=1003 actual=1002
PASS f32_receiver
error: semantic: method `marker_probe` not found on type `u64` (receiver value: 7)
```

```
SIMPLE_RUST_SEED_WARNING=0 SIMPLE_TIMEOUT_SECONDS=600 SIMPLE_EXECUTION_MODE=jit \
  nice -n 19 bin/simple run test/01_unit/language/probe_primitive_receiver_trait_impl_dispatch.spl
rc=70
PRIMITIVE_TRAIT_IMPL_DISPATCH PROBE: begin
Runtime error: Function 'str.marker_probe' not found
Runtime error: unresolved symbol -- this is a code-generation dispatch gap, not a program error. Refusing to substitute a placeholder value (it would render as the text 'error' and silently corrupt output).
```

Three live findings:

1. **i32 still collapses onto the i64 impl** under the seed interpreter
   (1002 where 1003 is correct). Matches the long-standing RED row.
2. **NEW: unsigned primitive Self types have no impl at all.** `impl MarkerProbe
   for u64` is accepted at parse/lower time but the receiver resolves to
   *nothing*: `method 'marker_probe' not found on type 'u64'`. This is a
   strictly worse failure than the i32 collapse (which at least reaches *an*
   impl) and was not previously recorded. Note the pure-Simple
   `primitive_type_key` DOES key unsigned distinctly (`-2000 - bits`), so this
   is a seed-side gap, not a Defect B gap.
3. **Defect A confirmed LIVE and now shown to be broader than `hash`.** Under
   the JIT every primitive receiver fails — `marker_probe` is not in the
   builtin table, so it fails CLOSED (rc=70) rather than silently, exactly as
   the original analysis predicted. The silent-open variant remains whatever
   name collides with the table at `closures_structs.rs:1780-1800`.
4. **Bonus, separate defect:** with the struct control arm ordered FIRST, the
   JIT died with `runtime error: invalid field receiver` and **SIGILL, core
   dumped (rc=132)** on `ControlPoint(x: 1).marker_probe()` — a `self.x` read
   inside a trait impl body. Filed here only as an observation; it is a
   distinct crash from the dispatch gap and is out of this row's scope.

### Root cause, by file:line

- Defect A (JIT, both the fail-closed and the silent-open variants):
  `src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs:1778-1800`
  — the `match method { ... }` name->runtime-function table has no
  receiver-type gate, and there is no fallback to a user `impl Trait for
  <primitive>` when the name is absent from it.
- Finding 2 (u64/unsigned): seed interpreter method dispatch,
  `src/compiler_rust/compiler/src/interpreter/expr/calls.rs` / `interpreter_method/mod.rs`
  — unsigned receiver values never consult the user impl table.

Both root causes are in `src/compiler_rust/**` (the Rust seed). This lane's
allowed edit scope was `src/compiler/{35.semantics,80.driver,99.loader,90.tools,60.mir_opt,25.traits}/**`;
the pure-Simple half in `35.semantics` is **already correct by content**, so
there was nothing left to fix there. **No source fix was made by this lane** —
recording root cause instead, per scope.

### Specs

- Reproducing spec (pre-existing, unchanged):
  `test/01_unit/language/primitive_receiver_trait_impl_dispatch_spec.spl`
- **NEW class-detection spec:**
  `test/01_unit/language/primitive_receiver_trait_impl_dispatch_class_spec.spl`
  — generalises the class: every primitive Self type (text, i64, i32, u64,
  bool, f32, f64) across BOTH engines, driven through a subprocess so the
  JIT-only half can actually go red. A spec body always runs interpreted, so
  the previous in-process-only spec was structurally incapable of catching
  Defect A.
- **NEW probe:** `test/01_unit/language/probe_primitive_receiver_trait_impl_dispatch.spl`

### Residual / NOT proven

- The Defect B fix in `35.semantics` is proven present **by content only**; it
  has never been executed. A bootstrap rebuild is still the only way to observe
  it, and this lane did not run one.
- `trait_impl_lowering.spl:249-251` bare-name registration for trait DEFAULT
  methods is still unfixed and untested.
- Native (`native-build`) column not re-probed this session.
- `bin/simple test` on the reproducing spec produced **1897 lines of warnings
  with no `Results:` line** on the first attempt — the known silent-exit0
  runner defect
  (`doc/08_tracking/bug/test_runner_emits_no_result_summary_silent_exit0_2026-08-17.md`).
  The `bin/simple run` transcripts above are therefore the authoritative
  evidence for this row, not the `test` runner.
- **Neither spec has a `Results:` line from this session — UNVERIFIED, not
  green and not red.** Three attempts on a box at load 80-130:
  `nice -n 19 bin/simple test test/01_unit/language/primitive_receiver_trait_impl_dispatch_spec.spl --timeout 900`
  -> 1942 lines, **exit code 0**, no `Results:`; retried once at
  `--timeout 1800` -> 1943 lines, **rc=143** (SIGTERM — killed under host
  load), no `Results:`. rc=143 with no `Results:` line is UNVERIFIED, not a
  failure; and the exit-0-with-no-summary on the first attempt is the
  silent-green signature — a caller checking only `rc` would have recorded this
  row as PASSING while nothing ran.

  **Both non-verdicts were host contention in SESSION SETUP, not the runner
  defect.** Given a slot, the runner completes normally and the actual spec
  execution takes ~4 seconds. The class spec proved this:

```
nice -n 19 bin/simple test \
  test/01_unit/language/primitive_receiver_trait_impl_dispatch_class_spec.spl --timeout 1800
rc=1

impl Trait for <primitive Self> reaches the user impl on every engine
  ✓ runs the probe at all under both engines
  ✗ dispatches to the matching impl for every primitive Self type under the interpreter
  ✗ dispatches to the matching impl for every primitive Self type under the cranelift JIT

3 examples, 2 failures
SPEC FILE VERDICT: ...class_spec.spl declared>=3 executed=3 passed=1 failed=2 dropped=0
Results: 3 total, 1 passed, 2 failed
Duration: 3848ms
```

  The class spec is therefore **genuinely RED (2 of 3)**, and red for exactly
  the right reason: the passing example is the non-vacuity guard (the probe
  really did start under both engines), while the two failures carry the
  interpreter and JIT transcripts quoted above verbatim in their diff output.
  Note `executed=3 dropped=0` — the run is not vacuous.

  The `child binary:` line in that transcript confirms the subprocess resolved
  to `/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`
  (the seed), never the production-guard wrapper.

- **The pre-existing reproducing spec still has no `Results:` line from this
  session.** A third attempt was launched and was still in session setup (1338
  lines of warnings, no verdict) when this lane stopped; it was NOT killed and
  NOT observed to fail. Its documented RED state (`Results: 7 total, 6 passed,
  1 failed`, the i32 row) is carried over from the original report, and its
  substance is independently confirmed by the `bin/simple run` interpreter
  transcript above (`FAIL i32_receiver expected=1003 actual=1002`). Treat the
  spec's `test`-runner verdict as re-confirmed only when someone quotes a fresh
  `Results:` line for it. Do not read this as a pass or a fail: the class spec's
  in-repo status is UNVERIFIED-BY-`test`, VERIFIED-RED-BY-`run` (its three
  `it` blocks assert exactly the `PASS ...` lines the probe transcripts above
  show absent).
