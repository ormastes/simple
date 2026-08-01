# "Unresolved type" family: lower_named_kind whitelist drift, not source defects

**Date:** 2026-08-01
**Status:** partially fixed (`usize`/`isize`/`u128`/`i128`/`unit` landed in `085dfec41`)
**Component:** `src/compiler/20.hir/hir_lowering/types.spl` — `HirLowering.lower_named_kind`

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
| `Int`     |     1093 |       167 |      599 |       108 | **no**   | **no** -> open               |
| `Self`    |      517 |        48 |      485 |        34 | yes      | **no** -> open               |
| `Bool`    |      352 |       103 |      297 |        76 | **no**   | **no** -> open               |
| `tuple`   |      313 |        65 |      220 |        58 | yes      | **no** -> open               |
| `dict`    |      101 |        21 |       36 |        10 | yes      | **no** -> open               |
| `Map`     |       56 |        21 |       40 |        13 | yes      | **no** -> open               |
| `HashMap` |       37 |        12 |       27 |         8 | yes      | **no** -> open               |
| `Vec`     |       37 |        11 |       35 |         9 | **no**   | **no** -> open               |
| `u128`    |       36 |         7 |       18 |         2 | yes      | **no** -> FIXED              |
| `set`     |       23 |        14 |       11 |        10 | yes      | **no** -> open               |
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

**Still open:** `tuple` (313 uses), `Self` (517 uses), `Map`/`HashMap`/`dict`/`set`
(217 uses). These need more than a scalar arm — `Self` requires real self-type
resolution (the seed calls `resolve_self_type()`), and the container names need a
decision between `Any` (seed behaviour) and a real `Dict`/`Tuple` kind. Not
attempted here.

Also unported from the seed: the single-uppercase-letter rule
(`name.len() == 1 && all ascii uppercase -> ANY`, which covers bare `T`/`K`/`V`
type params), the `has_X` / `X_opt` -> `Optional<X>` normalizations, and the
`global_struct_defs` cross-module struct fallback.

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

## Known divergence left open

`usize`/`isize` signedness follows `HirType.named` (unsigned/signed 64), **not**
the seed, which returns a signed `I64` for both. Observable only for `>>` on a
high-bit-set value: unsigned emits `ushr`, signed emits `sshr`. Recorded here
rather than silently normalized. The seed's own comment on `u128`/`i128` states
that picking `U64` there "would make the JIT emit ushr and silently diverge from
the interpreter on high-bit-set limbs" — the same reasoning may argue for signed
`usize`, but changing it would contradict this compiler's `HirType.named` and the
`u64` arm beside it. Needs a deliberate cross-engine decision.
