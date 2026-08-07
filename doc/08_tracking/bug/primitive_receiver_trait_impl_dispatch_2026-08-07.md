# Trait `impl` blocks on PRIMITIVE Self types are honoured only by the interpreter

- **Status:** OPEN (diagnosed, root cause located, not fixed) — re-verified
  2026-08-07 (same day, follow-up probe), matrix unchanged
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

## Unresolved axis (do not assert either way)

Whether the `i32`/`i8`/`i16` → `i64` collapse is "the `as` cast does not retype
the value" or "dispatch discards the integer width" is not settled by this data.
The bare-name registration at `trait_impl_lowering.spl:244` is the leading
suspect but was not proven.

## Suggested fix (not attempted — see why)

Defect B looks like a two-part change: key primitive impl registration on the
primitive's type kind rather than a bare name, and let `try_trait_method` fall
through to `try_trait_method_with_solver` instead of returning nil when the
receiver type carries no symbol.

Deliberately NOT attempted in this lane: `try_trait_method` is on the hot path of
every method resolution in the self-hosted compiler, and bootstrap stage 3 is
blocked, so there is no self-hosted binary on which the change could be verified.
The only available vehicle is `native-build` on toy probes, which cannot show a
regression in the compiler's own bootstrap. A speculative edit there would be
unverifiable by construction.

Defect A is a one-arm change in the disposable Rust seed (gate `"hash"` on the
receiver's static type, or drop the arm so it fails closed like every other
un-implemented primitive method). Filed rather than applied because the seed is
explicitly not the deliverable — but note that until it is fixed, **every
`.hash()` call on a primitive in JIT-compiled code silently returns 0**.

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
