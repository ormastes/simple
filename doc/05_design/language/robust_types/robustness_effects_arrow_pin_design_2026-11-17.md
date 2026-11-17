# Robustness Design: Tiers, Arrow Update, Immutable Contracts, Pin, Effect Summary

**Date:** 2026-11-17
**Branch:** `release/1.0.0` (source read at `fcf511af755`)
**Status:** Design. Owner decisions are report §1 (restated in the plan §0);
everything marked *proposed* here is a recommendation until selected.
**Plan:** `doc/03_plan/release/1.0.0/robustness_completion_plan_2026-11-17.md`
**Reuses:** `robust_types_layer_contracts_2026-11-12.md` (typestate, `NotInit<T>`,
absence policy), `doc/03_plan/compiler/data/immutable_views_async_init_revisions_2026-11-13.md`
(three read-only contracts), `doc/02_requirements/language/principles.md`.
No second typestate, effect or ownership system is introduced.

## 1. Tier policy (report §4)

Command spellings are **proposed**; none exists at the tip (lint has only
`LintEvidenceTier`, `src/compiler/90.tools/lint/_LintMain/config_and_model.spl:1177-1251`).

| Profile | Low | Medium | High | Use |
|---|---|---|---|---|
| normal `build`/`check`/`run` | on | off | off | edit/build/run loop |
| `build --diagnostic=medium` | on | on | off | cross-call/module diagnostics |
| `build --diagnostic=high` | on | on | on, bounded | proof attempts |
| default `lint` | on | on | on, bounded | comprehensive |
| `lint --fast` | on | off | off | labelled partial |
| robust CI | on | on | required on | coverage + completeness |

Tiers: **Low** = local AST/HIR checks, bounded local flow, resolved-contract
lookup. **Medium** = module dataflow, call-graph/SCC summaries, effect-row
inference. **High** = path-sensitive whole-program reasoning, SMT, termination.
Completeness is reported per rule as one of `pass | fail | incomplete |
timed_out | unsupported | not_applicable`; a run with an unfinished required
rule is never clean.

**Core soundness exception.** The tier policy governs *additional* analyses.
A mandatory validity check (type, ownership, initialization, effect boundary)
either succeeds within the normal budget, consumes exact-version evidence,
conservatively restricts the operation, or sits behind an explicit
unsafe/trusted boundary. It is never moved into optional lint.

## 2. Arrow update `x->method(args)` (report §5)

### 2.1 Current state
- Seed: `src/compiler_rust/parser/src/expressions/postfix.rs:577-593` builds
  `Expr::FunctionalUpdate` with a match-guard depth guard at `:580`.
- Self-hosted: `src/compiler/10.frontend/core/parser_expr.spl:32` imports
  `TOK_ARROW` but has no postfix branch; `parser_stmts.spl:2422` uses `->`
  only as the match-arm separator; no `FunctionalUpdate` node in
  `src/compiler/**/*.spl`. **Parity gap.**
- Spec/requirement mislabelled: `test/03_system/feature/usage/functional_update_spec.spl:60-158`
  asserts array/dict contents under struct/immutability titles.

### 2.2 Contract
`x->m(a, b)` is exactly `x = x.m(a, b)` with these rules:
1. **Writes the place, not the object.** Whether `m` mutates shared storage is
   decided by `m`'s receiver and effect contract. An immutable value-producing
   `m` leaves the old content unchanged; the binding receives the new value.
2. **Target must be an assignable place**: `var` local, field, index, deref
   that ordinary assignment accepts. `val` target, temporary
   (`make()->m()`), or non-place → named compile error. Phase one: only
   already-valid places.
3. **Single evaluation**: base, index, arguments each once, in documented
   order (base, index, args left-to-right), one call, one store. Lower through
   the existing compound-assignment place machinery; never duplicate the AST.
4. **Place validity**: arguments, callee, callbacks or suspension must not
   relocate the container or invalidate the captured field/index before the
   store. Reuse the ordinary assignment/call alias rules; no retained raw pointer.
5. **Type**: result must be assignable to the target's declared type. No unit
   erasure, no implicit error unwrap, no silent widening.
6. **`must_use`**: the assignment consumes the result; obligations inside `m`
   still apply.
7. **Fallible**: `x->try_m()?` is call → propagate error → store `T`. Without
   `?`, a `Result<T,E>` result into a `T` target is a type error. No store on
   error does not revive a consumed receiver; the method's own ownership rules
   apply. No transaction is implied; chained updates commit step by step.
8. **Async/effects/concurrency**: no hidden await, no purity, no atomic RMW.
   The resolved method's effect contract is the arrow's effect contract.
9. **Immutable contracts**: `Immutable<T>` handle rebinding is allowed; a write
   *through* the view is still IMM-01. `RevisionImmutable<T>` update yields a
   new revision handle; old readers keep theirs. `FrozenImmutable<T>` prior
   storage is never modified in place.
10. **Pin**: no move/replace of an address-sensitive pointee through the arrow.

### 2.3 Parsing
One `->` token. Contexts: function return type (`parser_decls_fn.spl:160,223`),
match-arm separator (`parser_stmts.spl:2422`), postfix update (to add in
`parser_expr.spl`, guarded as the seed does at depth of a pipe-guard arrow).
Regression cases: return-type arrow, guard arrow, lambda, generic args,
optional parentheses, malformed tail diagnostics. Cost: constant per arrow.

## 3. Canonical effect summary (report §9)

One versioned record per function/method instantiation, produced by the
compiler and consumed by interpreter, native, loader, LSP, lint, test runner:

```
EffectSummaryV1
  declared_upper:   [EffectKind]      # from attributes / registry
  verified_local:   [EffectKind]      # body facts (inference_effects.spl)
  callee_assumed:   [(callee_id, iface_digest, [EffectKind])]
  callback_effects: [(param_index, [EffectKind])]
  unresolved:       [(span, reason)]  # Unknown markers
  complete:         bool              # false if any Unknown (inference_effects.spl:114-115)
  policy_version, analysis_version, target_projection
```
Rules: missing facts stay `Unknown`, never pure/no-alloc/nonblocking.
Restricted regions (`nogc`, pure, nonblocking, interrupt) reject an unproven
incompatible effect or require an explicit trusted boundary; a warning cannot
establish the property. `Await` gets an explicit arm (today it falls to
`case _`). SCC fixpoints for recursion; row constraints for higher-order APIs
(medium tier). TLDR/SMF carry the summary; the loader rejects a stale or
weaker summary rather than degrading the caller. Effects are typed identities,
not strings. Kinds are target-neutral; backend allocation/sync behaviour is
recorded separately.

Loop bounds are part of the summary and must be proven, not shaped:
`effect_validation.spl:109-128` currently returns `LOOP_BOUND_CONST` for any
`Binary(_, _, IntLit)`; the fix requires operator ∈ {`<`,`<=`} with a monotone
induction step in the body, else `NONE`.

## 4. Three immutable contracts and the pin contract (report §6, §8)

| Contract | Write through? | Sees later alias writes? | Stable snapshot? | Cost |
|---|---|---|---|---|
| `Immutable<T>` | no | yes | no | read-only view; sync separate |
| `RevisionImmutable<T>` | no | no (pinned revision) | yes | lease metadata, retained versions, COW path |
| `FrozenImmutable<T>` | no | no | permanent | consume-to-freeze avoids copy; else detached copy |
| Pinned `T` (proposed) | per ownership | per access contract | not implied | fixed storage lifetime; no intrinsic heap |

Read-only ≠ snapshot ≠ fixed address ≠ race-free (principle P7).

**Pin contract (proposed, P1-A):** one address-stability contract integrated
with existing ownership (`55.borrow/borrow_check/hir_ownership.spl`,
`ownership_flow.spl`) and `NotInit<T>` initialization:
1. Movable values vs. values that entered an address-sensitive state.
2. Safe pin construction for stack, arena/pool and heap owners whose lifetime
   covers the pinned use.
3. No move, swap, ordinary copy or replacement through projected fields while
   self-references are live.
4. Field projection: structurally pinned fields vs. independently movable.
5. Drop/invalidation on cancellation, failed init, loader unload.
6. Phased construction: place → ordinary fields → internal refs → validate →
   publish; no partially initialized safe value escapes.
7. Prefer typed IDs/indices + generation for compiler nodes and command pools.
8. FFI/DMA: alignment, lifetime, device ownership, completion, memory order are
   separate obligations; CPU pinning is not DMA synchronization.
Cost: marker/ownership checks are Low; lifetime inference Medium/High and
never the only guard. A pin wrapper adds no allocation by itself.

## 5. `must_use` completion (report §7)

Obligation resolved in typed HIR (methods, trait dispatch, generic
substitution, imported summaries), carried in TLDR/SMF. Consumption = return,
assign, `?`, `match`, await, explicit `val _ =` with policy-governed reason.
Severity follows the safety ladder (`driver_safety_severity.spl:59-75`):
robust → Warn, critical/verified → Deny, else Advisory; a Deny is an admission
failure, not a string in `eval_warnings` (`eval_stmts.spl:174-191`). Direct
discard is Low tier, zero runtime; all-path consumption is Medium.
`must_use` is not linearity, completion or cleanup.

## 6. Shared architecture (report §15)

Frontend keeps syntax/spans/arrow context; typed HIR resolves identities,
units, transitions, effects, discard and place rules once; a summary layer
stores immutable versioned facts with completeness; MIR lowers arrow via place
machinery; backends/interpreter preserve the contract (parity tested); loader
verifies before replacement; lint/LSP consume cached IR and shared diagnostic
IDs. Cache keys include content/interface digests, instantiation, dependency
summary hashes, compiler/analysis/policy versions and target projection —
never timestamp, path or printed type name alone.
