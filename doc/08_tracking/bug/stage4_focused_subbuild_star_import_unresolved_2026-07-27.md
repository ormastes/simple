---
id: stage4_focused_subbuild_star_import_unresolved_2026-07-27
status: open
severity: high
discovered: 2026-07-27
discovered_by: full-bootstrap --deploy run from current origin main (Stage 4, full-CLI focused sub-builds)
related: src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl
related: src/compiler/50.mir/mir_data.spl
related: scripts/bootstrap/bootstrap-from-scratch.sh
fixed_by: 67024e9c0a51
---

# Stage 4 focused sub-builds fail star-import resolution; bootstrap deploy blocked

**Status:** open — bootstrap deploy did not occur; `bin/simple` still resolves to
the 2026-07-25 Rust seed (`bin/release/x86_64-unknown-linux-gnu/simple`, mtime
2026-07-25 05:30:43, size 145290352). Two root causes have since been found and
fixed in commit `67024e9c0a51`, cutting unresolved-name errors from 5,950 to
2,224, but stage 4 still fails overall (see "Remaining stage-4 blockers"
below), so no deploy has occurred yet.

## Summary

Stage 4 of `--full-bootstrap --deploy` now lowers all 1,752 HIR modules with
**zero segfaults** (the prior deterministic segfault at HIR module 32 is fixed —
see `doc/03_plan/agent_tasks/simple_riscv_hardening_2026-07-27.md` §6, commit
`9b612a11418c`). It then fails inside `focused native-build` sub-builds with
unresolved-name and untyped-return errors. Deploy never happens because the
focused-build phase does not reach a green state.

## Symbol histogram (top offenders, original measurement)

| Symbol | Count |
|---|---|
| `MirType` | 760 |
| `me` | 543 |
| `mir_operand_copy` | 393 |
| `MirTypeKind` | 317 |
| `MirConstValue` | 197 |
| `TokenKind` | 185 |
| `lex_make_token` | 160 |
| `MirOperand` | 158 |

These are overwhelmingly symbols reached through **star imports**, e.g. `use
compiler.mir.mir_data.*` in
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`.

## Original hypothesis — DISPROVEN

> Each `focused native-build` sub-build computes its own module closure (files
> it will parse/lower/codegen for that focus). The hypothesis was that this
> closure computation does not follow star imports (`use X.*`) the same way
> the whole-source / entry-closure build does, so modules like
> `compiler.mir.mir_data` (providing `MirType`, `MirTypeKind`,
> `MirConstValue`, `MirOperand`, …) and `compiler.lex.token` (`TokenKind`,
> `lex_make_token`) never get added to `modules_by_name` for the affected
> focus, and every star-imported name from them resolves as unknown.

**DISPROVEN by direct measurement.** Running with `SIMPLE_BOOTSTRAP_DIAG=1`
shows `compiler.mir.mir_data` reports `found=true` for its importers — it
**is** parsed and lowered as part of the focused build. There are only 127
total import-misses in the whole run, and `mir_data` is not among them. So the
module is present in the closure; the closure-computation theory does not
explain the failure. The real defect is downstream, in symbol
**registration**, not module discovery — see "Root causes found" below.

## Disproven hypotheses

1. **Per-focus closure omits star-imported modules** (the original hypothesis
   above). Disproven: `mir_data` is `found=true`, parsed, and lowered; only
   127 import-misses total, none of them `mir_data`.
2. **Struct-field map copy nil-fills nested dicts** (an earlier theory raised
   while investigating this failure class, tracked informally alongside
   `doc/08_tracking/bug/native_dict_get_struct_value_corrupt_option_2026-07-27.md`
   and
   `doc/08_tracking/bug/native_dict_len_returns_minus_one_2026-07-27.md`).
   Disproven by a direct probe: build a `Dict<text,i64>` inside a struct, put
   that struct into a map, pass the map through a function argument into
   another struct's field, and read `keys().len()` back at every step — it
   stayed `== 2` throughout, i.e. the nested dict survives the copy path
   intact. The earlier theory was an artifact of the broken `Dict.len()`
   (which always returned `-1`) and is falsified now that the working
   primitive (`keys()`) is used instead.

## Root causes found + fixes (commit `67024e9c0a51`)

Two distinct mechanisms, both in symbol registration for glob (`use X.*`)
imports, not in closure computation:

### 1. Facade export lists not swept for star imports

`src/compiler/50.mir/mir_data.spl` declares no `MirType` itself (verified: 0
matches for `struct MirType` in that file). Instead it does `use
compiler.mir.mir_types.*` / `use compiler.mir.mir_instructions.*` (lines
19-20) and re-exports via bare `export MirTypeKind, MirType, MirSignature,
MirConstValue` lines (line 630 and similar).

`register_glob_imported_symbols` only swept the six decl dicts plus the
facade's IMPORT ITEMS — but a star import has `items.len() == 0`, so that loop
body never executed for these names. Named imports already resolved
correctly through `find_reexport_source`; the glob path never did.

**Fix:** route each exported name through `register_imported_symbol` so both
the named-import and glob-import paths behave identically.

**Measured effect:** unresolved-name count 5,950 → 4,008; `MirType` alone
760 → 37.

### 2. Transitive star imports (one level) not surfaced

`use A.*` where `A` itself does `use B.*` must surface `B`'s decls to `A`'s
consumers. `mir_data` star-imports `mir_instructions` and never re-exports
`mir_operand_copy` (verified: 0 mentions of `mir_operand_copy` in
`mir_data.spl`; it is defined in `mir_instructions.spl`), yet consumers of
`use compiler.mir.mir_data.*` call it directly — 393 errors, same shape for
the `cranelift_*` helpers.

**Fix:** sweep one level deep, deliberately non-recursive.

**Measured effect:** unresolved-name count 4,008 → 2,224; `mir_operand_copy`
and `cranelift_*` fully cleared.

### Measurement table (unresolved-name error count)

| Stage | Unresolved names | Note |
|---|---|---|
| Earlier run, 159-commits-older tree | 11,826 | pre-HIR-segfault-fix baseline |
| Post-HIR-segfault-fix, pre this fix | 5,950 (+166 untyped-return) | this bug's original filing |
| After fix 1 (facade export sweep) | 4,008 | `MirType` 760 → 37 |
| After fix 2 (one-level transitive star) | 2,224 | `mir_operand_copy`/`cranelift_*` cleared |

## OPEN CAVEAT — needs a decision, not yet resolved

Fix 2 **broadens** glob visibility: names from a star-imported module's own
star imports are now visible one level up, which they were not before.
Current call sites depend on this today, but they may only have been relying
on a **pre-fix accident**: before the recent native `Dict` fixes, a corrupt
`Dict.get()` registered every looked-up name as an opaque `Class` symbol (see
`doc/08_tracking/bug/native_dict_get_struct_value_corrupt_option_2026-07-27.md`),
which could have been masking missing-import errors in a different way.

The alternative reading is that these call sites should carry **explicit
imports** instead of relying on transitive glob visibility, and that widening
glob semantics papers over that. This is **measured to reduce errors**, it is
**not proven to preserve the intended resolution targets** (i.e., that the
name each call site binds to is the same symbol it would bind to with an
explicit import). Flag for a design decision before this is considered fully
resolved.

## Remaining stage-4 blockers (independent of import resolution, both pre-existing)

1. **`me` unresolved (543 occurrences).** `me`, the method-receiver keyword,
   is reported as an unresolved NAME 543 times — byte-identical across two
   different trees (159 commits apart) and two different compiler builds,
   and unchanged by both import-resolution fixes above. This is not a
   star-import symptom; it needs its own bug doc and root-cause pass.
2. **Module-key canonicalization.** The same physical file is registered
   under multiple spellings of its module key (numbered/unnumbered/dotted),
   e.g. `compiler.10.frontend.core.lexer`, `compiler.frontend.core.lexer`,
   `compiler.core.lexer`. The lexer family (`TokenKind` 185,
   `lex_make_token` 160, `lex_advance` 116, `lex_peek` 70) still fails on
   this. These are **named** imports (`use
   compiler.frontend.core.lexer.{...}`), not globs, so they are outside the
   scope of fixes 1 and 2 above.

## Overall trajectory

Unresolved-name error count: 11,826 → 5,950 → 4,008 → 2,224. All 1,752 HIR
modules lower with zero segfaults throughout. Stage 4 still **FAILS** overall
(the two remaining blockers above), so no deploy has occurred and `bin/simple`
remains the 2026-07-25 seed.

## Reproduce

```sh
sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy
```

Run from a worktree at current `main`. Stage 4 log:
`build/bootstrap/logs/x86_64-unknown-linux-gnu/stage4-native-build.log`
(evidence for this run; job path
`/home/ormastes/.claude/jobs/4403a7d8/tmp/wt-bootstrap/build/bootstrap/logs/x86_64-unknown-linux-gnu/stage4-native-build.log`).
For the registration-vs-closure diagnostics used to disprove the original
hypothesis, re-run with `SIMPLE_BOOTSTRAP_DIAG=1` and grep the log for
`found=true`/import-miss markers for `compiler.mir.mir_data`.

## Impact

Bootstrap deploy is blocked at Stage 4 for the full-CLI focused-build path.
`bin/simple` remains the 2026-07-25 Rust seed. Every gate that requires the
redeployed self-hosted binary (RISC-V hardening campaign gates, and any other
consumer of `bin/simple`) stays seed-attributed until this is fully fixed
(both remaining blockers above cleared, and the open caveat resolved).

## Next diagnostics

1. File a dedicated bug doc for the `me`-as-unresolved-name defect (543,
   deterministic) and bisect the site(s) that misreport it — likely inside
   method-body name resolution or error recovery, not star-import handling.
2. Fix module-key canonicalization so the lexer family's named imports
   resolve regardless of which spelling (`compiler.10.frontend.core.lexer`
   vs `compiler.frontend.core.lexer` vs `compiler.core.lexer`) a given
   `use` statement uses.
3. Resolve the open caveat above: decide whether one-level transitive glob
   visibility is the intended semantic, or whether call sites relying on it
   should get explicit imports instead — verify against pre-`Dict`-fix
   behavior to rule out the masking-accident explanation.

---

## Triage re-verification 2026-08-17 (c_mir lane, classified by CONTENT not SHA)

**Governing fact for every 50.mir-attributed row:** nothing runnable on this
host executes `src/compiler/50.mir/**.spl`. `bin/simple` resolves to
`bin/release/x86_64-unknown-linux-gnu/simple` (59536728 bytes, mtime
2026-08-16 22:59), whose own `--version` banner states it is a Rust
**bootstrap seed**; it has its own Rust MIR/JIT/native pipeline and never reads
`src/compiler/**.spl` for compilation logic. `bin/release/simple` is the
2181-byte refusing production-guard wrapper, and no stage2/stage3 self-hosted
binary exists under `build/bootstrap/`. Therefore any evidence in this doc
phrased as "reproduced on `bin/simple`" is evidence about the **seed**, not
about 50.mir, and the runtime claim here can only be closed by a full
self-hosted bootstrap (not run: the user's bootstrap is live and
`build/bootstrap/**` is off-limits). Rows were therefore classified by
grepping current source.

**Verdict: MIS-ATTRIBUTED — NOT A 50.mir DEFECT.**

Both root causes are glob-import symbol registration in 20.hir —
`src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl:739`
(`register_imported_symbol`) and `:1095` (`find_reexport_source`).
`src/compiler/50.mir/mir_data.spl` is only the victim facade (its `export` lines
`:733-735`). `register_glob_imported_symbols` has zero matches anywhere in
`src/compiler`. Re-attribute this row to 20.hir module lowering.

---

## Triage 2026-08-17 (bug-triage lane) — STILL OPEN, and the stamp above is partly WRONG

### The 2026-08-17 c_mir stamp's central factual claim is FALSE

> "`register_glob_imported_symbols` has zero matches anywhere in `src/compiler`."

It has **nine**, starting with its own definition:

```
$ /usr/bin/grep -rn "register_glob_imported_symbols" src/compiler/
src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl:1541:    me register_glob_imported_symbols(...)
                                              :1548, :1557, :1779   (call sites)
src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl:1559:    me register_glob_imported_symbols_depth(...)
                                              :1620, :1702          (recursive calls)
src/compiler/20.hir/hir_lowering/types.spl:148                      (per-ROOT memo)
src/compiler/10.frontend/core/parser_decls_use.spl:237              (reference)
```

Anyone reading that stamp would conclude the function had been deleted and the
described fix no longer exists. It exists and is live. The stamp's *verdict*
(mis-attributed to 50.mir; belongs to 20.hir module lowering) is nonetheless
**correct and is retained** — it just was not established by the evidence it
cites. Fixed here rather than left to mislead the next triager.

### Claims re-derived from CURRENT source

| claim in this doc | 2026-08-17 by content |
|---|---|
| Fix 1 — facade export lists swept for star imports | **PRESENT.** `register_glob_imported_symbols` -> `register_glob_imported_symbols_depth`, `module_lowering.spl:1541-1557`. |
| Fix 2 — one-level transitive star sweep | **PRESENT and since GENERALIZED.** The sweep is now a `depth`-parameterised recursion (`:1559`, recursing at `:1620` and `:1702`), no longer capped at one level; the runaway is bounded by the per-ROOT memo documented at `hir_lowering/types.spl:148` (GLB2, 2026-08-01). The "deliberately non-recursive" wording above is therefore **stale** — and note this makes the OPEN CAVEAT *broader*, not narrower: glob visibility now reaches arbitrarily deep, so the undecided question of whether call sites should carry explicit imports instead applies to more of them than when the caveat was written. |
| Remaining blocker 2 — module-key canonicalization | **IMPLEMENTED.** Three canonicalizers now fold every dotted spelling of one physical file onto one name by dropping all-digit tier segments and folding `std.` -> `lib.`: `_driver_canonical_module_name` (`80.driver/driver_source_loading.spl:196`), `hir_pkg_canonical_module_name` (`module_lowering.spl:84`, which also accepts a repo-relative PATH spelling), and `module_surface_canonical_module_name` (`hir_lowering/module_surface.spl:1058`). The doc's own three example spellings (`compiler.10.frontend.core.lexer` / `compiler.frontend.core.lexer` / `compiler.core.lexer`) are exactly what rule 1 folds, and the driver docstring records the fold as verified collision-free over every `src/**/*.spl`. This blocker is retired **by content**; whether the lexer-family counts (`TokenKind` 185, `lex_make_token` 160, ...) actually went to zero is a RUNTIME question, unanswered — see below. |
| Remaining blocker 1 — `me` unresolved x543 | **UNVERIFIABLE HERE, and its follow-up was never actioned.** "Next diagnostics" item 1 asked for a dedicated bug doc; `doc/08_tracking/bug/` contains no `me`-as-unresolved-name row (the ~20 `me`/receiver rows there are all interpreter/JIT receiver-binding defects, a different family). Not filed from this lane, which owns only this row. |
| OPEN CAVEAT (glob widening may paper over missing explicit imports) | **STILL UNDECIDED.** No design decision recorded anywhere in the tree; see the widened-scope note above. |

### Why this row is NOT closed

Every number in this doc is a stage4 focused-sub-build measurement, and that
build was **not** re-run: `bin/simple` resolves to
`bin/release/x86_64-unknown-linux-gnu/simple`, the **Rust seed** (59,536,728
bytes, mtime 2026-08-16 22:59), which has its own Rust pipeline and never reads
`src/compiler/**.spl` as compiler logic; no self-hosted stage2/stage3 binary
exists in this checkout; and `build/bootstrap/**` was off-limits (another lane's
bootstrap was live). So the headline claim — "stage 4 still FAILS overall" —
can be neither confirmed nor retired here, and the unresolved-name count is
unknown at current tip.

No source change and no specs from this lane: both surviving mechanisms live in
`src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl`, which is owned by
another lane in this session. Re-attributed to 20.hir module lowering (per the
retained verdict above); the `related:` front-matter still points at 50.mir and
should be corrected by whoever picks this up.
