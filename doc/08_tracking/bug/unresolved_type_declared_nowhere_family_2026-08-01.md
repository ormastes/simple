# "Unresolved type" family: lower_named_kind whitelist drift, not source defects

**Date:** 2026-08-01
**Status:** Class A **closed except the cross-module struct fallback**.
Scalars (`usize`/`isize`/`u128`/`i128`/`unit`) landed in `085dfec41`;
`Self`, `tuple`, `Map`/`HashMap`/`dict`/`set`, the single-uppercase-letter rule
and `has_X` landed in the follow-up commit that added this paragraph.
Class B remains blocked on an owner decision.
**Component:** `src/compiler/20.hir/hir_lowering/types.spl` — `HirLowering.lower_named_kind`
(plus `20.hir/hir_lowering/_Items/module_lowering.spl` for the `Self` scope fix)

## Summary

A stage4 A/B run reported 1,484 `unresolved type` errors and framed the two
largest buckets — `Int` (x187) and `usize` (x66) — as **source defects**: "types
that are used but declared nowhere in the tree", unfixable by any resolver
change.

That framing is **wrong for `usize` and right for `Int`**. The distinction
matters because acting on the original framing would have meant rewriting ~1,300
`usize` annotations to `i64`, discarding signedness and normalizing a workaround
around a compiler bug.

## The actual mechanism

`lower_named_kind` is the **single strict gate** that emits
`unresolved type: {name}`. It matches a hardcoded whitelist of type names and
falls through to `self.symbols.lookup_or_invalid(name)`; a miss is a hard error
that collapses the declaration to `HirTypeKind.Error`.

That whitelist has **drifted from the Rust seed's resolver**
(`src/compiler_rust/compiler/src/hir/lower/type_resolver.rs`). The seed accepts a
strictly larger set of bare scalar/container names.

Critically, **no seed-driven probe can detect the drift**. The seed resolves any
unknown type name to `ANY` under `lenient_types`, so both `simple_seed run` and
`simple_seed compile ... -o out.smf` accept a deliberately bogus type, exit 0,
and emit an artifact. Verified directly: a probe annotated
`ZzzNotARealTypeQqq` compiled to a present `.smf` with `rc=0`. Only driving
`HirLowering` in-process and asserting `errors.len()` gates this.

## Census (owned `.spl`, excluding `src/compiler_rust/vendor/**`, `src/runtime/vendor/**`)

Type-position uses (`: N`, `-> N`, `[N]`, `<N,..>`), string literals and
comments stripped:

| name      | all uses | all files | src uses | src files | in seed? | in pure-Simple (before fix)? |
|-----------|---------:|----------:|---------:|----------:|----------|------------------------------|
| `usize`   |     1303 |       146 |     1194 |       131 | yes      | **no** -> FIXED              |
| `Int`     |     1093 |       167 |      599 |       108 | **no**   | **no** -> open (Class B)     |
| `Self`    |      517 |        48 |      485 |        34 | yes      | **no** -> FIXED              |
| `Bool`    |      352 |       103 |      297 |        76 | **no**   | **no** -> open (Class B)     |
| `tuple`   |      313 |        65 |      220 |        58 | yes      | **no** -> FIXED              |
| `dict`    |      101 |        21 |       36 |        10 | yes      | **no** -> FIXED              |
| `Map`     |       56 |        21 |       40 |        13 | yes      | **no** -> FIXED              |
| `HashMap` |       37 |        12 |       27 |         8 | yes      | **no** -> FIXED              |
| `Vec`     |       37 |        11 |       35 |         9 | **no**   | **no** -> open (Class B)     |
| `u128`    |       36 |         7 |       18 |         2 | yes      | **no** -> FIXED              |
| `set`     |       23 |        14 |       11 |        10 | yes      | **no** -> FIXED              |
| `unit`    |       16 |        15 |        7 |         6 | yes      | **no** -> FIXED              |
| `Float`   |       12 |         9 |        5 |         4 | **no**   | **no** -> open               |
| `Char`    |        9 |         5 |        9 |         5 | **no**   | **no** -> open               |
| `i128`    |        1 |         1 |        0 |         0 | yes      | **no** -> FIXED              |
| `isize`   |        0 |         0 |        0 |         0 | yes      | **no** -> FIXED (parity)     |

The stage4 per-name counts (187, 66) are far below these totals because that run
**aborts inside phase 3** on a separate arena desync (6,474 `[stmt_get_tag] OOB`
/ `arena_len=0` events, first on log line 1). Its counts are early-abort
artifacts and were **not** used as evidence here. Stage3 is also useless for
this: it runs the bootstrap-flat pipeline and never performs this lowering.

## Class A — compiler parity gap (NOT source defects)

`usize`, `isize`, `u128`, `i128`, `unit`, `tuple`, `Self`, `Map`, `HashMap`,
`dict`, `set`. The seed accepts all of these. For `usize` specifically, three
further layers of *this* compiler already handle it:

- `HirType.named` (`20.hir/hir_types.spl`) -> `Int(bits:64, signed:false)`;
  `isize` -> `Int(bits:64, signed:true)`
- `30.types/_TypeLayout/{layout_core,arch_and_verify}.spl` -> 8 bytes
- `70.backend/target/riscv32.spl` -> 4 bytes; `80.driver/shb/shb_types.spl`
  registers a `usize` layout entry

Only `lower_named_kind` lacked the arm. **Fixed in `085dfec41`** for the scalar
subset (`usize`/`isize`/`u128`/`i128`/`unit`).

### Follow-up: remaining Class A gaps closed

Every remaining Class A name now resolves. Each arm below states the type it
maps to and whether that matches the seed:

| spelling | maps to | seed parity |
|----------|---------|-------------|
| `Self` | the enclosing class / impl type, `HirTypeKind.Named(owner, [])` | **exact** — seed `resolve_self_type()` returns `current_class_type` |
| `tuple` | `HirTypeKind.Tuple([])` (empty element list) | **exact** — seed registers `HirType::Tuple(vec![])` |
| `Map` / `HashMap` with 2 args | `HirTypeKind.Dict(k, v)` | **exact** — seed `type_resolver.rs:459` |
| `Map` / `HashMap` argless | `HirTypeKind.Any` | **exact** — seed `:182` / `:464` |
| `dict` / `set` | `HirTypeKind.Any` | **exact** — seed `:182` |
| single uppercase letter (`T`/`K`/`V`) | `HirTypeKind.Any` | **exact** — seed `:141` |
| `has_X` | `HirTypeKind.Optional(lower(X))` | **exact** — seed `:128` |

No arm changes signedness or width, so the divergence recorded below stays
confined to `usize`/`isize`.

**Ordering is load-bearing, not incidental.** In the seed, `tuple`, the bare
container names and the single-letter rule all sit **after**
`self.module.types.lookup(name)`; only `has_X` (and the `?` suffix) run before
it. That order is reproduced exactly, because this tree really does declare
types named `Map` (1 struct), `HashMap` (2 classes + 1 struct) and `Set`
(2 structs) — hoisting those names into the match above the symbol lookup would
shadow real user types and silently retype their annotations to `Any`. A
regression spec (`lets a really declared Map struct win over the bare-container
rule`) pins this. `has_X` is safe to run before the lookup only because **no**
type in the tree is declared `has_*` (verified by declaration grep).

### `Self` was not a table entry — root cause

`Self` needed a second fix, in a different file. `lower_named_kind` already had
the context it needed (`current_method_self_type`, the exact analogue of the
seed's `current_class_type`), but the annotation was being resolved **before**
any class/impl scope was entered.

The mechanism, **PROVED** by dumping the parsed module rather than inferred: the
parser desugars a method-carrying `class C:` into a class whose method dict is
**empty**, plus a synthetic `impl` block (`classes["Widget"].methods` empty while
`module.impls.len() == 1`). Class methods therefore flow through the impl-method
branch of the up-front signature-declaration pass in
`module_lowering.spl`, which runs at **module scope** where
`current_method_self_type` is still nil. The class-body scope
(`declaration_lowering.spl:528`) and the impl scope
(`trait_impl_lowering.spl:199`) are both established later and so could never
help a `-> Self` in a *signature*.

Fix: publish the self-type around that signature loop, reusing the owner symbol
the loop already computed for `method_symbol_name`, saved/restored exactly like
the two existing scopes. A single instrumented run confirmed `Self` was reached
exactly once and with a nil context, which is what localised this.

**Still open — the cross-module struct fallback.** The seed falls back to
`global_struct_defs` for a struct used by name without an explicit `use`
(`type_resolver.rs:151`). This is the one rule that is **not** portable as a
table entry: pure-Simple HIR lowering has **no `global_struct_defs` equivalent
at all** (grep for `global_struct`/`global_defs` over `src/compiler/**` returns
nothing). Porting it means building and threading a cross-module struct
registry, which is a design change rather than a parity patch, so it is left
open deliberately rather than approximated.

Correction to the previous revision of this doc: there is **no seed `X_opt`
normalization**. The seed has exactly two name rewrites, a `?` *suffix*
(`:119`) and a `has_` *prefix* (`:128`); `resolve_type_opt` (`:502`) is an
unrelated helper that resolves an absent `Option<Type>` AST annotation to
`VOID`. The earlier `X_opt` claim was a misreading of that function name.

## Class B — genuine source defects (capitalized-primitive dialect)

`Int` (1093), `Bool` (352), `Float` (12), `Char` (9). Accepted by **neither**
resolver.

These are **not** N independent bugs — they are **one dialect**, and it is
already half-blessed: `lower_named_kind` has
`case "text" | "str" | "String": HirTypeKind.Str`, so the capitalized `String`
spelling from the same dialect **already resolves**. The affected files use the
spellings together in single signatures, e.g.
`fn name_lint_parse_class(trimmed: String, indent: Int, line_num: Int)`
(`src/compiler/90.tools/lint/_LintMain/name_lints.spl:71`). Fixing `Int` but not
`String` in either direction leaves the tree incoherent.

Two further amplifiers, both confirmed:

1. **Tier mirroring.** `src/lib/{gc_async_mut,nogc_async_mut,nogc_sync_mut}/`
   each hold a copy of the `lsp/` and `dap/` trees, and `src/app/dap/` mirrors
   them again — so `protocol.spl` alone contributes 17 uses x 4 copies. A fix
   must be applied across mirrors or it will regress.
2. **Test-tree mirroring.** `test/03_system/feature/...` and
   `test/feature/...` are duplicate paths with identical counts (27/27, 21/21,
   19/19, 17/17).

**Decision required before acting** (deliberately not taken unilaterally):

- **Option A — alias in the compiler.** Add `Int`/`Bool`/`Float`/`Char` arms
  next to the existing `String` arm. Two lines, no source churn, internally
  consistent with `String`. Risk: blesses a dialect that
  `35.semantics/lint/primitive_types.spl` explicitly calls the "canonical
  bare-primitive type table -- SINGLE SOURCE OF TRUTH" and lists as
  lowercase-only, with parity enforced by
  `test/01_unit/compiler/lint/primitive_types_parity_spec.spl`.
- **Option B — rewrite use sites.** `Int`->`i64`, `Bool`->`bool`, and for
  coherence `String`->`text`. Matches the canonical table, but touches ~1,450
  sites across ~170 mirrored files, and `String` currently compiles — so this is
  a behaviour-preserving churn on the `String` half and a fix only on the rest.

`Vec` (37 uses) is a third case: a Rust spelling with no counterpart in either
resolver and no `String`-style precedent. Likely a genuine port artifact; should
become `[T]`.

## Evidence standard used

All findings are **static and local**. The parity gap is provable by reading the
two whitelists; the census is a grep over owned `.spl` with string/comment
stripping, using `/usr/bin/grep` (the default `grep` here is ugrep). The fix
carries an in-process A/B:

- with fix: **5 passed, 0 failed**
- without fix: **1 passed, 4 failed** (only the rejection control stays green)
- no parse regression: baseline and edited both reach the same semantic stage
  with an identical `56 function(s) contain` message

`test/01_unit/compiler/hir/seed_parity_scalar_type_names_spec.spl` carries a live
control asserting an undeclared name is still rejected, matched by **error
identity** rather than a count (the same annotation is reported once per
lowering pass, so a fixed count is brittle — the first draft of that control
asserted `1` and saw `2`).

### Follow-up evidence (`Self`/`tuple`/containers/single-letter/`has_X`)

`test/01_unit/compiler/hir/seed_parity_container_and_self_types_spec.spl`,
in-process A/B, **both directions**:

- with fix: **8 passed, 0 failed**
- without fix (both implementation files reverted to the base commit, spec
  unchanged): **3 passed, 5 failed** — and the 3 that stay green are exactly
  the three controls (undeclared name still rejected, `TK` still rejected,
  declared `Map` struct still wins). Every parity example goes red; no control
  moves in either direction.
- the pre-existing scalar spec still reports **5 passed, 0 failed** with the
  follow-up applied, so `085dfec41` is not regressed.

Three controls, not one, because two distinct weakenings had to be excluded:
accepting any unknown name (the `lenient_types` failure mode), and implementing
the single-letter rule without its `len() == 1` guard — which would have erased
whole undeclared type names like `TK` to `Any` while still passing the original
control.

**Harness non-vacuity was proved by sabotage before any of the above was
believed.** Renaming the landed `case "usize"` arm to a dead label turned the
scalar spec red (`3 passed, 2 failed`, exit 1), confirming the runner really
recompiles the edited pure-Simple source rather than serving a cached or seed
-resolved result.

**Two measurement traps hit and documented, so the next lane does not repeat
them:**

1. *Seed-as-host is fine; seed-as-oracle is the trap.* These specs are executed
   by the Rust seed binary, but the resolver under test is the pure-Simple
   `lower_named_kind` driven in-process — the seed only interprets the spec. That
   is not the false-green described above, and the sabotage run proves it.
2. *Directory-mode runs are void here.* `simple test test/01_unit/compiler/hir/`
   reports `44 total, 0 passed, 44 failed` with **no per-example `✗` lines** —
   and reports **exactly the same at the base commit**, unchanged by any edit.
   It is a pre-existing harness artifact of running many specs in one process
   (`parse_module_silent_checked` does not reset state between files), not a
   regression signal. Per-file verdicts require **one process per file**; the
   directory number must never be quoted as a result.

## Known divergence left open

`usize`/`isize` signedness follows `HirType.named` (unsigned/signed 64), **not**
the seed, which returns a signed `I64` for both. Observable only for `>>` on a
high-bit-set value: unsigned emits `ushr`, signed emits `sshr`. Recorded here
rather than silently normalized. The seed's own comment on `u128`/`i128` states
that picking `U64` there "would make the JIT emit ushr and silently diverge from
the interpreter on high-bit-set limbs" — the same reasoning may argue for signed
`usize`, but changing it would contradict this compiler's `HirType.named` and the
`u64` arm beside it. Needs a deliberate cross-engine decision.
