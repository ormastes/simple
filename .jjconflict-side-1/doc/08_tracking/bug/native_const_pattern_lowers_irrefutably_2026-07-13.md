# Native `Const` pattern lowers irrefutably

**Status (2026-07-16):** RESOLVED — enum-variant-name precedence guard landed; native prints CONST_ARM/OTHER_ARM correctly (native-authoritative: the seed itself takes the const arm for both). Parity case: const_pattern_refutable.
path). The 2026-07-15 "source fixed" claim applied only to the Rust seed's HIR
lowering; the pure-Simple compiler that `native-build` interprets live had NO
subject-enum precedence and still reinterpreted a bare `case Const(...)` as an
irrefutable struct pattern. A candidate root fix is now in place (see
Regression evidence) but could NOT be runtime-verified: `native-build` is
globally broken at this commit (see blocker below).

## Symptom

In a native SimpleOS compiler, a `MirInstKind.Const(dest, _, _)` match arm accepted non-`Const` values and treated the enum header as `LocalId`. The filesystem compiler faulted in `var_reassign_local_id_value` after MIR lowering.

## Evidence

The failing ELF omitted a `Const` discriminator check and loaded word zero from the enum object. A guarded implementation that first compares `rt_enum_discriminant` numerically emits `rt_enum_payload`, `rt_index_get(0)`, then the `LocalId` accessor and advances past this fault.

## Required fix

Fix native pattern lowering for keyword-named, multi-field enum variants. Add a target-code regression proving a standalone first `Const` arm checks its discriminator and extracts payload fields. Then remove the allocation-heavy marker workaround in `var_reassign_analysis.spl` and measure warm optimizer latency/RSS.

## Resolution (2026-07-15)

Expression and statement match lowering now give a variant owned by the
subject enum precedence over an unrelated same-named struct. The focused tests
`test_subject_enum_const_variant_beats_unrelated_const_struct` and
`test_standalone_match_subject_enum_const_variant_beats_unrelated_const_struct`
require both the discriminator check and payload extraction.

The temporary `MirInstKind.Const` marker plus `rt_enum_discriminant` workaround
was reverted before this fix and is absent from the current
`var_reassign_analysis.spl`; therefore there is no retained marker allocation
or optimizer performance delta to remove or measure. Executing the focused
tests remains the only closure evidence still pending.

## Regression evidence (2026-07-16)

Re-verified against commit `8ac25987333`. The bug is STILL PRESENT in the
pure-Simple source.

Root cause: `src/compiler/20.hir/hir_lowering/expressions.spl`
`lower_pattern` (case `Enum`, ~line 890) reinterpreted a bare positional
pattern `case Const(dest, _, _):` as a `HirPatternKind.Struct` whenever a
struct/class named `Const` was registered — with NO check for whether the
subject enum owns a `Const` variant. As a `Struct` pattern the arm never
reaches `build_match_expr`'s `has_enum` branch, so the match desugars to an
irrefutable if-chain (`desugar_match_to_if_chain`) and the `Const` arm is
ALWAYS taken. Silent-wrong: no discriminator check, later arms unreachable.

Oracle reproduction (seed interpreter, `bin/simple run`):
- Subject `enum Inst { Const(i64,i64,i64), Other }` + unrelated `class Const`.
  `case Const(dest,_,_)` on `Inst.Const(42,..)` → `CONST_ARM` (correct); on
  `Inst.Other` → `CONST_ARM` (WRONG, should be the `_` arm). Renaming the class
  to a non-colliding name makes both correct — confirming the collision is the
  trigger. (The seed exhibits the same bug, so the oracle is NOT a clean
  reference for this exact case; correctness is unambiguous from language
  semantics.)

Candidate root fix (in this change, UNVERIFIED at runtime — see blocker):
add an `enum_variant_names` set to `HirLowering` (types.spl), populate it in the
`module_lowering` pre-scan from `module.enums[*].variants[*].name`, and guard
the struct reinterpretation with `and not self.enum_variant_names.has(variant)`.
Safe-by-construction: the guard only narrows the struct-reinterpretation branch,
so a mis-populated/empty set degrades to the prior behavior (never a NEW
regression); when populated it gives a subject-owned enum variant precedence
over an unrelated same-named struct, matching the Rust focused tests.

Verification BLOCKER (not this bug): `native-build` is globally broken at this
commit — it fails to compile ANY program (native-smoke-matrix: total=15 pass=0
fail=15) with `error: semantic: type mismatch: cannot convert dict to int` at
`src/compiler/10.frontend/core/aop_predicate_parser.spl:104:32`
(`while start < s.len() and s[start] == " "` — `text` indexing mis-typed by the
interpreted compiler's own semantic check). Until that regression is fixed,
neither the native-vs-oracle protocol nor the native-smoke-matrix gate can run,
so this candidate fix cannot be closed. Filed/owned by the native-build
self-check lane.
