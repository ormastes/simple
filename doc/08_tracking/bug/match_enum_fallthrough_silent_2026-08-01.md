# A `match` on an enum that falls through every arm is silent

- **ID:** BUG-2026-08-01-match-fallthrough
- **Date:** 2026-08-01
- **Status:** diagnostic landed WARN-ONLY; full enforcement deferred (cost enumerated below)
- **Severity:** high — silent wrong answer, no diagnostic on any lane

## Summary

A `match` whose scrutinee matches **no arm** takes no branch and emits nothing.

- **Statement form** — silent no-op. Execution continues past the `match` as if
  it were not there.
- **Expression form** — silently yields nil, which reads back as the **integer
  3** under the nil-sentinel encoding. This is a wrong *value*, not just a
  missing effect, and it propagates.

## Reproduction (PROVED)

Probes: `scratchpad/repro/m1.spl` (statement), `m2.spl` (expression). One
process per file.

```
enum Kind: A / B / C
match k:            # k = Kind.C
    case Kind.A: ...
    case Kind.B: ...
```

| Lane | Command | Statement form | Expression form |
|---|---|---|---|
| Rust seed, JIT (default) | `simple_seed run f.spl` | falls through, no output | `expr_result=3` |
| Rust seed, forced interp | `simple_seed run f.spl --interpret` | falls through | `expr_result=3` |
| `simple.pre-segv-fix-20260731`, `run` | `... run f.spl` | falls through | `expr_result=3` |
| bare positional | `simple_seed f.spl` | falls through | `expr_result=3` |

Exit status **0** in every cell. No stderr diagnostic in any cell.

**Lane caveat (do not overstate):** every binary reachable at this tip prints
the `bootstrap seed only` banner, so all four rows above are Rust-seed lanes.
The pure-Simple interpreter's own fall-through code was reached and exercised
separately, as `.spl` source, via the new spec (see Verification).

## Where it lives

| Layer | Site | Behaviour before this change |
|---|---|---|
| Pure-Simple interp, **expression** | `src/compiler/10.frontend/core/interpreter/eval.spl:770` | pushed `"...no arm matched value of type <kind>"` — names only the runtime KIND, not the enum, value, arms or location |
| Pure-Simple interp, **statement** | `src/compiler/10.frontend/core/interpreter/eval_stmts.spl:642` | **nothing at all** — bare `val_make_nil()` |
| MIR enum lowering | `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`, no-default path | last `next_block` gotos merge; merge emits `const 0`. No trap, no `Unreachable`, no diagnostic |
| Rust seed, statement | `src/compiler_rust/compiler/src/interpreter_control.rs:4732` | `Ok((Control::Next, None))` — silent |

**All compile-time exhaustiveness machinery in-tree is dead code:**

| File | Entry point | Callers |
|---|---|---|
| `src/compiler/35.semantics/lint/match_exhaustiveness.spl:85` | `check_match_exhaustiveness` | **NO CALLERS** (re-exported only) |
| `src/compiler/70.backend/backend/exhaustiveness_validator.spl:156` | `ExhaustivenessValidator` | **NO CALLERS** |
| `src/compiler/95.interp/interpreter/pattern.spl:127` | `PatternAnalysis.analyze_match` | not called by the interpreter |

A live but text/regex-heuristic lint exists at `src/app/cli/query_lint_checks.spl:14`
(warning-only, not AST-based).

## Why the runtime report is the load-bearing half

The obvious fix is a compile-time exhaustiveness check. **It would not have
caught the instance that motivated this bug.**

In that instance the arms *textually covered every variant*. The value's variant
tag came from a **different enum of the same bare name** (an enum variant named
`Style` colliding with a `tui/style.spl` struct, a layout-renderer class and two
`llm_caret` classes), resolved through the global bare-name registry. A checker
built on that same registry inspects the wrong enum and passes.

This is not hypothetical, and it is not rare. The blast-radius scan measured:

- **1,410** distinct enum names declared in-tree
- **336** enum names declared **more than once**
- Of the 286 candidate non-exhaustive match sites, **223 (78%)** name an enum
  whose bare name is declared more than once

The scan itself hit the failure: it had to merge variant sets across
same-named enums, so 223 of its 286 findings are of unknown accuracy. **The
measurement tool and the proposed checker fail the same way, for the same
reason.** Only a runtime report — which observes the actual value — is immune.

**Decision:** runtime diagnostic is primary; compile-time is a secondary,
warn-only backstop. Not the textbook answer, and deliberately so.

## Blast radius (deliverable)

Scan over the tip tree, `.spl` only, vendored paths excluded
(`src/compiler_rust/vendor/`, `src/runtime/vendor/`). Counts an enum `match`
with **no** wildcard/`else`/bare-binder arm that omits at least one variant.

| Metric | Count |
|---|---|
| `.spl` files scanned | 33,104 |
| `match` blocks total | 34,136 |
| **Non-exhaustive enum match, no wildcard** | **286** |
| ...enum name declared more than once (result unreliable) | 223 |
| ...enum name unique (reliable finding) | **63** |
| ...of those, owned `src/` excluding `src/compiler_rust/` | **24** |

By area: `src/lib` 68, `src/compiler_rust` 52, `test/01_unit` 44, `test/unit` 41,
`src/compiler` 21, `test/03_system` 16, `src/app` 16.

Full 286-row enumeration: `scratchpad/enumeration.md` (regenerate with
`scratchpad/blast.py`).

### Real findings among the 63 reliable sites

These are genuine non-exhaustive matches on unambiguously-named enums. They are
findings, not noise — each silently yields nil-as-3 on an uncovered variant:

- `src/lib/nogc_sync_mut/redis/client.spl` — **11 sites** (lines 80, 99, 118,
  136, 155, 174, 195, 214, 233, 252) on `RedisReply`, most covering only 2 of 6
  variants. An unexpected reply type is silently read as `3`.
- `src/lib/common/encoding/bencode.spl` — 4 sites (470, 518, 530, 580) on
  `BencodeValue`, 4 of 5 variants.
- `src/lib/nogc_sync_mut/src/core/context_manager.spl` — 3 sites (229, 239, 249)
  on `TransactionState`, each covering 1 of 3.
- `src/app/office/word/word_app.spl:157` — `UIEvent`, **1 of 27** variants.
- `src/app/llm_dashboard/data/agent_position.spl:73` — `RoomKind`, 3 of 7.
- `src/lib/nogc_async_mut/fs_driver/instance.spl:45` — `DriverInstance`, 4 of 5.
- `src/lib/common/ui/form_factor.spl:133` — `DeviceClass`, missing `Tablet`.
- `src/app/interpreter/expr/advanced.spl:27` — `FStringPart`.

## What was changed

Warn-only, strictly additive. No existing behaviour was weakened and no
existing gate, assertion or timeout was relaxed.

1. `src/compiler/10.frontend/core/interpreter/eval_tables.spl` — new
   `match_fallthrough_message(...)` (pure, testable), `match_arm_covered_variants(...)`,
   `report_match_fallthrough(...)`, and an opt-in `match_fallthrough_set_abort(bool)`.
   The message names **the enum, the value, the covered arms and the module
   path**, and switches wording to an explicit *bare-name collision* note when
   the failing variant is textually covered.
2. `src/compiler/10.frontend/core/interpreter/eval.spl` — new
   `val_enum_variant_name(...)`; expression fall-through now reports through
   `report_match_fallthrough` instead of the kind-only string.
3. `src/compiler/10.frontend/core/interpreter/eval_stmts.spl` — statement
   fall-through now reports at all (previously nothing).
4. `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl` — an enum
   match lowered with no default arm now records a non-fatal lowering
   diagnostic naming the enum, the covered arms, the missing variants and the
   span. Message deliberately does **not** start with `"enum match:"`, which is
   on the `_mir_error_is_fatal` allowlist in
   `src/compiler/80.driver/driver_pipeline_lowering.spl:119` — starting with it
   would have failed the build at all 286 sites.

Default mode is warn. `match_fallthrough_set_abort(true)` opts a caller into a
hard error at the interpreter tier.

## Verification

- `test/unit/compiler_core/interpreter/match_fallthrough_diagnostic_spec.spl` —
  **9 examples, 9 passed** under `simple_seed test` (tree-walking interpreter,
  executing the edited `eval_tables.spl` as source).
- **Sabotage test:** stubbing `match_fallthrough_message` to a constant turns
  **8 of 9** examples RED. (The 9th is a negative assertion, which a constant
  trivially satisfies.) The spec asserts message *content*, which no merge or
  backfill path can restore.
- **UNVERIFIED BY EXECUTION:** the MIR change (item 4) and the compiled/JIT
  lanes. No binary at this tip can be rebuilt in-session, and stage-3 self-host
  is independently broken. Item 4 is inspected, not run.

## Interaction with the enum-payload sub-pattern defect

Separate, already-documented defect: nested `Enum`/`Literal` payload
sub-patterns always match and never bind (`case E.I(5)` fires on `E.I(7)`).
Reproduced here on both seed binaries to check the interaction:

```
E.I(7) -> "five"     # wrong: payload defect, arm fired when it should not
E.S("x") -> FELLTHROUGH   # correct fall-through, would now be reported
```

**The payload defect MASKS this one.** Where a constant-payload arm wrongly
matches, no fall-through occurs and the new diagnostic stays quiet. The fix for
the payload defect is already present in source at this tip
(`enum_deep_flags` routing in `switch_operators_calls.spl`) though not in the
probe binaries. Once binaries carry it, **fall-through reports will increase** —
that is the correct direction, not a regression.

## Cost of full enforcement (deferred)

Promoting the MIR diagnostic from `self.error` to `self.error_fatal` — which the
`error_fatal` docstring itself prescribes for exactly this shape ("every site
that continues past the error and emits a placeholder operand (a const 0/3...)")
— would fail the build at up to **286** sites. Sequencing:

1. Fix the **63** reliably-identified sites (24 in owned `src/`), starting with
   the 11 in `redis/client.spl`.
2. Resolve the **336** duplicated enum names, or give the checker a
   collision-aware resolver. Until then a compile-time error is unsound in both
   directions — it will both miss real collisions and fire on false ones.
3. Only then promote to `error_fatal`, and add an `Unreachable` MIR terminator
   in place of the `const 0` placeholder.

Step 2 is the blocker, and it is the same global bare-name registry implicated
in the originating layout bug.

## Related

- `doc/08_tracking/bug/` — enum payload sub-pattern always-matches (separate defect)
- `src/compiler/80.driver/driver_pipeline_lowering.spl:119` — `_mir_error_is_fatal` allowlist
