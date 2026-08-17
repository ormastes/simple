# A `match` on an enum that falls through every arm is silent

- **ID:** BUG-2026-08-01-match-fallthrough
- **Date:** 2026-08-01
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
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


## 2026-08-01 follow-up: worklist re-scan and owned-`src/` fixes

### The original blast scan's wildcard predicate was wrong (PROVED)

The 286-site scan counted a match as having no wildcard unless it saw `case _`.
Three arm forms it missed are real, working catch-alls. Measured on the seed
(`bin/simple_seed`, rebuilt from origin tip `f93c9b2623`), each with a positive
control proving the probe was live, across `run`, `run --interpret` and bare
positional lanes:

| Form | Verdict | Probe |
|---|---|---|
| `_:` (no `case` keyword) | **real wildcard**, statement *and* expression form | `probe_wildcard.spl`, `probe_else.spl` |
| bare lowercase binder, e.g. `other:` | **real wildcard** | `probe_binder.spl` |
| `_ => expr` (arrow arm) | **real wildcard** | re-scan delta |
| `else:` | **PARSE ERROR** in a match arm, not a wildcard | `probe_else.spl` |

**Consequence: every named finding in the original worklist was a false
positive.** All 11 `redis/client.spl` sites already carry a `_:` arm; so do
`bencode.spl`, `context_manager.spl` and `word_app.spl:157`. None were changed
— changing them would have been churn on correct code.

`fs_driver/instance.spl:45` was a false positive of a different kind: it is the
"Example dispatch" block inside the enum's **docstring**, not code. The real
`impl DriverInstance` methods all cover `DbFs`.

### Corrected scan

Re-scanned the same tree with a corrected predicate (wildcard forms above;
`pub enum` / `export enum` declarations recognised — the original missed these,
which is why `TaskKind` and `ExecutionMode` resolved to the *wrong* same-named
enum; docstrings masked; `|` alternation and `=>` arms parsed paren-aware).

| Metric | Original | Corrected |
|---|---|---|
| `.spl` files scanned | 33,104 | 33,148 |
| `match` blocks | 34,136 | 30,341 |
| Non-exhaustive enum match, no wildcard | 286 | **477** |
| ...enum name declared more than once (unreliable) | 223 | **421** |
| ...enum name unique (reliable) | 63 | **56** |
| ...owned `src/`, actionable | 24 | **0 remaining** (10 found, 10 fixed) |

The corrected total is *higher* (477 vs 286) because recognising `pub enum`
raised the known-variant sets. The reliable slice is smaller and different.

### Measured fall-through behaviour by return type

The bug doc's `expr_result=3` holds for an `i64` expression context. Other
contexts differ, and the difference matters when judging severity:

| Return type | Fall-through result (seed interpreter) |
|---|---|
| `i64` expression | integer `3` (nil sentinel) |
| `bool` | `false` — control: a covered arm returned `true` |
| `text` | interpolation collapses; the **entire** surrounding string prints empty |
| struct | nil, then **faults** on first field access ("field access on nil receiver", SIGILL) |
| statement form | no-op; prior variable values retained |

### Fixed — 14 match sites across 10 files, all explicit variant arms, no wildcards added

| File | Enum | Added |
|---|---|---|
| `src/lib/nogc_sync_mut/ui/session.spl` | `UIEvent` | `CompositionUpdate`, `CompositionCommit` |
| `src/lib/common/ui/web_render_api.spl` | `UIEvent` | `CompositionUpdate`, `CompositionCommit` |
| `src/lib/nogc_async_mut/mcp/dispatch.spl` | `GateDecision` | `Hold` -> `"gated"` |
| `src/os/machine_profile.spl` | `SimpleOsFirmwareContractKind` | `BareMetal` -> `"bare-metal"` |
| `src/app/office/slides/render.spl` (x2) | `SlideElementKind` | `TableEl` |
| `src/app/llm_dashboard/data/agent_position.spl` (x2) | `RoomKind` | total `_room_key`, replacing two partial matches |
| `src/app/llm_dashboard/tui/colors.spl` (x2) | `RoomKind` | `Tasks` |
| `src/app/llm_dashboard/tui/room_map.spl` (x2) | `RoomKind` | `Tasks` (+ `tasks_room_furniture` in `office_furniture.spl`) |
| `src/app/llm_dashboard/gui/room_map_html.spl` (x2) | `RoomKind` | `Tasks` (+ `.room-tasks` CSS) |

Two of these are **live, exercised** fall-throughs, not latent:

- `UIEvent.CompositionCommit` is dispatched into `session.dispatch` from
  `src/os/compositor/compositor.spl:757` and
  `src/os/compositor/host_gui_event_router.spl:211`. The handler match at
  `session.spl:338` had no arm for it, so every IME commit took no branch.
- `SimpleOsFirmwareContractKind.BareMetal` is constructed at three lanes in
  `src/os/port/_SimpleosMultiplatformBuild/platform_target_catalog.spl`.

`RoomKind` behaviour was measured, not assumed: `_same_room(Skills, Skills)`
returned **false** (control `_same_room(Chat, Chat)` returned true), so
`pos_agents_in_room` returned an empty list for four of the seven rooms. An
earlier draft of this note claimed the fall-through was *truthy* and merged
different rooms; that was **wrong** and the probe disproved it.

### Verification

- All 10 edited files parse on the seed. **Sabotage control:** removing a colon
  from one added arm turns the gate RED with a parse error; restoring it returns
  it to GREEN. The gate is not vacuous.
- Corrected re-scan after the edits: actionable owned-`src/` sites **10 -> 2**,
  and both survivors are the collision-blocked ones below.
- **NOT verified by execution:** the edited modules were not run end-to-end;
  their imports do not resolve standalone, and no binary at this tip detects a
  missing enum variant. Parse + scan-delta + targeted behavioural probes on
  extracted enum shapes are the evidence. Claims above are labelled accordingly.

### Blocked, not fixed — the duplicate-name problem

**421 of the 477** sites name one of the **387 enum names declared more than
once** (of 1,590). Which enum's variant set applies cannot be determined without
resolving the collision, so these are **left untouched by design**. Guessing
would be exactly the failure mode this bug documents.

Two owned-`src/` sites are blocked for the same reason even though their enum
name looked unique — the arms name variants that do not exist in the only
declared enum of that name, so the site is resolving to some other `enum`:

- `src/app/interpreter/expr/advanced.spl:27` — matches `FStringPart.ExprFormatted`,
  but the sole declared `FStringPart` has `ExprWithFormat` and no `ExprFormatted`.
- `src/app/interpreter/module/evaluator.spl:81` — matches `Node.ArchitectureRule`,
  `Node.LeanBlock`, `Node.HandlePool` etc., none of which exist in
  `src/compiler/10.frontend/ast.spl`'s `Node`.

### Tracked list — all 56 unique-enum-name sites

Every remaining reliable site, enumerated rather than sampled. All owned-`src/`
production sites are fixed; the remainder are test fixtures and the two blocked
sites above.

| # | Site | Enum | Missing variants | Disposition |
|---|---|---|---|---|
| 1 | `src/app/interpreter/expr/advanced.spl:27` | FStringPart | ExprWithFormat | BLOCKED - bare-name collision (arms name variants absent from the only declared enum) |
| 2 | `src/app/interpreter/module/evaluator.spl:81` | Node | Other | BLOCKED - bare-name collision (arms name variants absent from the only declared enum) |
| 3 | `test/01_unit/common/ui/input_event_conformance_spec.spl:72` | UIEvent | CompositionCommit, CompositionUpdate, Copy, Cut, DragDrop, DragMove, DragStart, FetchResult, FocusEvent, InputChange, MouseEvent, Paste, PasteFromHistory, ScrollEvent | NOT FIXED - test fixture, intentionally partial |
| 4 | `test/01_unit/doctest/parser_spec.spl:27` | Expected | Empty, Exception | NOT FIXED - test fixture, intentionally partial |
| 5 | `test/01_unit/doctest/parser_spec.spl:48` | Expected | Empty, Output | NOT FIXED - test fixture, intentionally partial |
| 6 | `test/01_unit/doctest/parser_spec.spl:57` | Expected | Empty, Output | NOT FIXED - test fixture, intentionally partial |
| 7 | `test/01_unit/doctest/parser_spec.spl:101` | Expected | Empty, Exception | NOT FIXED - test fixture, intentionally partial |
| 8 | `test/01_unit/doctest/parser_spec.spl:131` | Expected | Empty, Exception | NOT FIXED - test fixture, intentionally partial |
| 9 | `test/01_unit/doctest/parser_spec.spl:139` | Expected | Empty, Exception | NOT FIXED - test fixture, intentionally partial |
| 10 | `test/01_unit/doctest/parser_spec.spl:147` | Expected | Empty, Output | NOT FIXED - test fixture, intentionally partial |
| 11 | `test/01_unit/doctest/parser_spec.spl:156` | Expected | Empty, Output | NOT FIXED - test fixture, intentionally partial |
| 12 | `test/01_unit/lib/common/compress_shared_helpers_spec.spl:23` | CompressionError | CorruptData, Other, OutputTooSmall, Unsupported | NOT FIXED - test fixture, intentionally partial |
| 13 | `test/01_unit/lib/common/compress_utilities_spec.spl:28` | CompressionError | CorruptData, Other, OutputTooSmall, Unsupported | NOT FIXED - test fixture, intentionally partial |
| 14 | `test/01_unit/lib/common/lz4_spec.spl:15` | CompressionError | CorruptData, Other, OutputTooSmall, Unsupported | NOT FIXED - test fixture, intentionally partial |
| 15 | `test/01_unit/lib/common/xz_lzma2_spec.spl:17` | CompressionError | CorruptData, Other, OutputTooSmall, Unsupported | NOT FIXED - test fixture, intentionally partial |
| 16 | `test/01_unit/lib/common/zstd_bits_spec.spl:15` | CompressionError | CorruptData, Other, OutputTooSmall, Unsupported | NOT FIXED - test fixture, intentionally partial |
| 17 | `test/01_unit/lib/common/zstd_compressed_block_spec.spl:6` | CompressionError | CorruptData, Other, OutputTooSmall, Unsupported | NOT FIXED - test fixture, intentionally partial |
| 18 | `test/01_unit/lib/common/zstd_dictionary_spec.spl:209` | CompressionError | CorruptData, Other, OutputTooSmall, Unsupported | NOT FIXED - test fixture, intentionally partial |
| 19 | `test/01_unit/lib/common/zstd_fse_spec.spl:13` | CompressionError | CorruptData, Other, OutputTooSmall, Unsupported | NOT FIXED - test fixture, intentionally partial |
| 20 | `test/01_unit/lib/common/zstd_fse_weights_spec.spl:47` | CompressionError | CorruptData, Other, OutputTooSmall, Unsupported | NOT FIXED - test fixture, intentionally partial |
| 21 | `test/01_unit/lib/common/zstd_huf_spec.spl:14` | CompressionError | CorruptData, Other, OutputTooSmall, Unsupported | NOT FIXED - test fixture, intentionally partial |
| 22 | `test/01_unit/lib/common/zstd_sequence_fse_execution_spec.spl:5` | CompressionError | CorruptData, Other, OutputTooSmall, Unsupported | NOT FIXED - test fixture, intentionally partial |
| 23 | `test/01_unit/lib/common/zstd_sequence_fse_tables_spec.spl:5` | CompressionError | CorruptData, Other, OutputTooSmall, Unsupported | NOT FIXED - test fixture, intentionally partial |
| 24 | `test/01_unit/lib/common/zstd_sequence_header_spec.spl:5` | CompressionError | CorruptData, Other, OutputTooSmall, Unsupported | NOT FIXED - test fixture, intentionally partial |
| 25 | `test/01_unit/lib/common/zstd_sequence_rle_spec.spl:5` | CompressionError | CorruptData, Other, OutputTooSmall, Unsupported | NOT FIXED - test fixture, intentionally partial |
| 26 | `test/01_unit/lib/common/zstd_single_sequence_compress_spec.spl:118` | CompressionError | CorruptData, Other, OutputTooSmall, Unsupported | NOT FIXED - test fixture, intentionally partial |
| 27 | `test/01_unit/lib/nogc_sync_mut/compression/brotli/brotli_negative_large_edge_spec.spl:32` | CompressionError | CorruptData, Other, OutputTooSmall, Unsupported | NOT FIXED - test fixture, intentionally partial |
| 28 | `test/02_integration/core/common_compression_framework_facade_spec.spl:35` | CompressionError | CorruptData, Other, OutputTooSmall, Unsupported | NOT FIXED - test fixture, intentionally partial |
| 29 | `test/cert/tool_qual/known_defects/nonexhaustive_match.spl:10` | E | B | NOT FIXED - test fixture, intentionally partial |
| 30 | `test/integration/core/common_compression_framework_facade_spec.spl:35` | CompressionError | CorruptData, Other, OutputTooSmall, Unsupported | NOT FIXED - test fixture, intentionally partial |
| 31 | `test/unit/common/ui/input_event_conformance_spec.spl:72` | UIEvent | CompositionCommit, CompositionUpdate, Copy, Cut, DragDrop, DragMove, DragStart, FetchResult, FocusEvent, InputChange, MouseEvent, Paste, PasteFromHistory, ScrollEvent | NOT FIXED - test fixture, intentionally partial |
| 32 | `test/unit/doctest/parser_spec.spl:27` | Expected | Empty, Exception | NOT FIXED - test fixture, intentionally partial |
| 33 | `test/unit/doctest/parser_spec.spl:43` | Expected | Empty, Output | NOT FIXED - test fixture, intentionally partial |
| 34 | `test/unit/doctest/parser_spec.spl:52` | Expected | Empty, Output | NOT FIXED - test fixture, intentionally partial |
| 35 | `test/unit/doctest/parser_spec.spl:95` | Expected | Empty, Exception | NOT FIXED - test fixture, intentionally partial |
| 36 | `test/unit/doctest/parser_spec.spl:129` | Expected | Empty, Exception | NOT FIXED - test fixture, intentionally partial |
| 37 | `test/unit/doctest/parser_spec.spl:137` | Expected | Empty, Exception | NOT FIXED - test fixture, intentionally partial |
| 38 | `test/unit/doctest/parser_spec.spl:145` | Expected | Empty, Output | NOT FIXED - test fixture, intentionally partial |
| 39 | `test/unit/doctest/parser_spec.spl:154` | Expected | Empty, Output | NOT FIXED - test fixture, intentionally partial |
| 40 | `test/unit/lib/common/compress_shared_helpers_spec.spl:23` | CompressionError | CorruptData, Other, OutputTooSmall, Unsupported | NOT FIXED - test fixture, intentionally partial |
| 41 | `test/unit/lib/common/compress_utilities_spec.spl:28` | CompressionError | CorruptData, Other, OutputTooSmall, Unsupported | NOT FIXED - test fixture, intentionally partial |
| 42 | `test/unit/lib/common/lz4_spec.spl:15` | CompressionError | CorruptData, Other, OutputTooSmall, Unsupported | NOT FIXED - test fixture, intentionally partial |
| 43 | `test/unit/lib/common/xz_lzma2_spec.spl:17` | CompressionError | CorruptData, Other, OutputTooSmall, Unsupported | NOT FIXED - test fixture, intentionally partial |
| 44 | `test/unit/lib/common/zstd_bits_spec.spl:15` | CompressionError | CorruptData, Other, OutputTooSmall, Unsupported | NOT FIXED - test fixture, intentionally partial |
| 45 | `test/unit/lib/common/zstd_compressed_block_spec.spl:6` | CompressionError | CorruptData, Other, OutputTooSmall, Unsupported | NOT FIXED - test fixture, intentionally partial |
| 46 | `test/unit/lib/common/zstd_dictionary_spec.spl:209` | CompressionError | CorruptData, Other, OutputTooSmall, Unsupported | NOT FIXED - test fixture, intentionally partial |
| 47 | `test/unit/lib/common/zstd_fse_spec.spl:13` | CompressionError | CorruptData, Other, OutputTooSmall, Unsupported | NOT FIXED - test fixture, intentionally partial |
| 48 | `test/unit/lib/common/zstd_fse_weights_spec.spl:47` | CompressionError | CorruptData, Other, OutputTooSmall, Unsupported | NOT FIXED - test fixture, intentionally partial |
| 49 | `test/unit/lib/common/zstd_fse_weights_spec.spl:114` | CompressionError | CorruptData, Other, OutputTooSmall, Unsupported | NOT FIXED - test fixture, intentionally partial |
| 50 | `test/unit/lib/common/zstd_huf_spec.spl:14` | CompressionError | CorruptData, Other, OutputTooSmall, Unsupported | NOT FIXED - test fixture, intentionally partial |
| 51 | `test/unit/lib/common/zstd_sequence_fse_execution_spec.spl:5` | CompressionError | CorruptData, Other, OutputTooSmall, Unsupported | NOT FIXED - test fixture, intentionally partial |
| 52 | `test/unit/lib/common/zstd_sequence_fse_tables_spec.spl:5` | CompressionError | CorruptData, Other, OutputTooSmall, Unsupported | NOT FIXED - test fixture, intentionally partial |
| 53 | `test/unit/lib/common/zstd_sequence_header_spec.spl:5` | CompressionError | CorruptData, Other, OutputTooSmall, Unsupported | NOT FIXED - test fixture, intentionally partial |
| 54 | `test/unit/lib/common/zstd_sequence_rle_spec.spl:5` | CompressionError | CorruptData, Other, OutputTooSmall, Unsupported | NOT FIXED - test fixture, intentionally partial |
| 55 | `test/unit/lib/common/zstd_single_sequence_compress_spec.spl:118` | CompressionError | CorruptData, Other, OutputTooSmall, Unsupported | NOT FIXED - test fixture, intentionally partial |
| 56 | `test/unit/lib/nogc_sync_mut/compression/brotli/brotli_negative_large_edge_spec.spl:32` | CompressionError | CorruptData, Other, OutputTooSmall, Unsupported | NOT FIXED - test fixture, intentionally partial |

By area: src/app 2, test/01_unit 25, test/02_integration 1, test/cert 1, test/integration 1, test/unit 26

## Related

- `doc/08_tracking/bug/` — enum payload sub-pattern always-matches (separate defect)
- `src/compiler/80.driver/driver_pipeline_lowering.spl:119` — `_mir_error_is_fatal` allowlist
