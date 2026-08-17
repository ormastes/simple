# `me` (receiver) reported as an unresolved NAME in class methods during stage-4 lowering

**Status:** **PARTIAL — fix landed for the dominant shape; 20 `me` errors remain
UNFIXED and UNINVESTIGATED.** Do not treat this row as closed.

> ~~**Status:** fixed (residual 20 — see Remaining)~~
> **SUPERSEDED 2026-08-17.** `fixed` contradicted this document's own
> `## Remaining` section, which states the residual 20 are "Not yet
> investigated. Follow-up needed." A row with an uninvestigated residual is
> PARTIAL, not fixed.

## Status correction 2026-08-17 (source inspection only)

**What the status claimed:** `fixed (residual 20 — see Remaining)`.

**What was actually verified** (2026-08-17, by reading this document and current
source; no compiler, test, or build was run — SOURCE INSPECTION ONLY, and
existing status stamps were treated as claims, not evidence): the document's own
body at `## Remaining` (line 101 ff.) says *"20 `me` errors survive — likely a
different shape (e.g. `me` inside a nested/lambda scope, or a class whose
receiver type failed to resolve). **Not yet investigated.** Follow-up needed."*
The `Measured` block reports `unresolved name: me`: 543 → 20, i.e. a **96.3%
reduction, not elimination**.

**Corrected to: PARTIAL.** Precisely:

- **FIXED:** the dominant shape — `me.field` member access and `me.method()`
  calls inside `me`-declared class methods, which accounted for 523 of the
  original 543 errors. Stage-4 side effects also confirmed in-doc: all 1,752 HIR
  modules lower, zero segfaults, total stage-4 unresolved 2,224 → 1,681.
- **NOT FIXED:** the residual **20** `unresolved name: me` errors. Shape unknown;
  hypothesised to be `me` in a nested/lambda scope or a class whose receiver type
  failed to resolve. **Never investigated** — no root cause, no repro isolated,
  no owner. The residual count of 20 is itself a stale in-doc figure that has not
  been re-measured since; re-measuring requires a stage-4 build, which this
  correction deliberately did not run.

### Traps for whoever fixes this later

- **(a) A renamed-away repro proves nothing.** The `ce` repro in
  `src/app/office/pptx_export.spl` was RENAMED AWAY — `grep -c '\bce\b'` on that
  file is now `0`; the identifiers are `pic_end` (`:526`) and `tce`
  (`:423,424,427,431`). Since the residual `me` errors were all in
  `src/app/office/*`, re-running office files as a regression check can look
  green purely because the triggering identifiers were renamed. The parser fix
  is nonetheless real and present at
  `src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl:487-491`.
- **(b) Do not cite `3c4e6551b7a` as the `ce`/`Grid` fix.** That commit
  ("fix(parser): 11 soft keywords could not be used as identifiers") covers
  `auto bind by examples export into lazy mod move on onto requires skip spawn
  unwrap use where with` — verified from its own test file
  `src/compiler_rust/parser/tests/contextual_keyword_identifiers.rs`. Neither
  `ce` nor `Grid` is in it.
**Found:** 2026-07-27 (RISC-V hardening campaign, Lane H — stage-4 full-CLI bootstrap)
**Area:** HIR lowering (`src/compiler/20.hir/`), bootstrap/stage-4 path
**Severity:** high — 543 errors; one of the two remaining stage-4 full-CLI blockers

## Finding

During the stage-4 full-CLI native build, HIR lowering emits

```
error: focused native-build: HIR lowering error in app.office.word.word_app: unresolved name: me
```

**543 times**, i.e. `me` — the method-receiver keyword — is being resolved as an
ordinary identifier and failing.

The source is ordinary, idiomatic Simple. `src/app/office/word/word_app.spl`:

```simple
class WordApp:
    ...
    me build_ui() -> UITree:
        """Build the full iOS-styled document editor UI tree."""
        val toolbar = me.build_toolbar()
        val sidebar = with_flex(me.build_sidebar(), 1)
        if me.sidebar_visible:
            ...
```

Both member access (`me.sidebar_visible`) and method calls (`me.build_toolbar()`)
are affected.

## Root cause

Simple has **two receiver syntaxes**:

- the parameter-list form: `fn foo(me):` — receiver explicitly declared as a
  parameter named `me`;
- the declaration-prefix form: `me foo():` — no explicit receiver parameter.

For the prefix form with no explicitly declared receiver parameter, the
class-body parser (`src/compiler/10.frontend/core/parser_decls_use.spl`,
`parse_class_body_method`, the else-branch around line 457) synthesizes the
receiver parameter named **`"self"`**, not `"me"` — see the code that builds
`method_param_names: [text] = ["self"]`.

Meanwhile `me` is **not handled in the expression parser at all**:
`TOK_KW_ME` appears only in declaration parsing
(`parser_decls_types.spl`, `parser_decls_use.spl`), never in
`parser_expr.spl`. So `me.field` / `me.method()` inside a method body falls
through the parser's keyword-as-identifier path and becomes `Ident("me")`.

HIR then looks up a symbol named `me`, which was never defined for
prefix-form methods (the synthesized receiver is named `self`), and
`lower_unresolved_ident` errors with `unresolved name: me`.

This explains the app/office vs compiler asymmetry noted in the original
finding: compiler code predominantly uses the parameter-list form (receiver
actually named `me`, so `Ident("me")` resolves), while `src/app/office/*`
classes use the prefix form (receiver synthesized as `self`, so
`Ident("me")` fails).

## Why invisible outside stage 4

Only observable under `SIMPLE_BOOTSTRAP_STAGE4=1`. Without that flag the
driver takes `bootstrap_lower_to_mir_context`
(see `src/compiler/80.driver/driver.spl` ~line 1107) and builds MIR from the
flat-AST accumulator, never surfacing HIR lowering errors.

**Proof:** the identical full build with only that flag removed reached
codegen with **zero** unresolved names (`me`=0, unres=0).

**Consequence:** isolated probes could not detect this. A standalone
`class Counter: me bump()...` probe compiled AND RAN correctly (printed the
right values), and so did a direct build of
`src/app/office/word/word_app.spl`, and a build with it as a non-entry
closure member, and one with `--low-memory`. All reported 0 errors. Anyone
re-investigating must reproduce through a real stage-4 build (entry
`src/app/cli/main.spl`), because the STAGE4 flag is rejected with any other
entry ("Stage4 entry must be src/app/cli/main.spl or src/app/os/main.spl").

## Fix

Landed in commit `8af2dc555960`: receiver aliasing in
`lower_unresolved_ident` (`src/compiler/20.hir/hir_lowering/expressions.spl`)
— when `me` or `self` fails to resolve, try the counterpart via
`lookup_or_invalid` before erroring.

No change to parameter layout, so it cannot reintroduce the
duplicate-receiver defect documented at that site
(`native_me_receiver_no_mutate`).

Measured:
- `unresolved name: me`: 543 → 20
- total stage-4 unresolved: 2,224 → 1,681
- all 1,752 HIR modules lower
- zero segfaults

## Remaining

20 `me` errors survive — likely a different shape (e.g. `me` inside a
nested/lambda scope, or a class whose receiver type failed to resolve). Not
yet investigated. Follow-up needed.

## Evidence

### Distribution (original, at time of finding — 543 total)

All occurrences were in `src/app/office/*` applications; no compiler module
reported it, although compiler classes use `me` methods extensively.

| module | count |
|---|---|
| `app.office.sheets.sheets_app` | 80 |
| `app.office.word.word_app` | 55 |
| `app.office.planner.planner_app` | 44 |
| `app.office.mail.mail_app` | 43 |
| (others) | remainder of 543 |

### Pre-existing, and independent of import resolution

The 543 count was **byte-identical** across:

- 2026-07-27 morning run — tree at `4eb553c720e`, compiler built with the
  (later reverted) partial-module guard rounds;
- 2026-07-27 afternoon run — tree 159 commits newer, compiler built with the
  `contains_key` + index-read fix (`9b612a11418c`).

Two different trees, two different compiler builds, identical count. It was
therefore unaffected by the `Dict.get()`/`Dict.len()` defects
(`native_dict_get_struct_value_corrupt_option_2026-07-27.md`,
`native_dict_len_returns_minus_one_2026-07-27.md`) and by the glob-import fixes
(`67024e9c0a51`), which moved the overall unresolved count 11,826 → 5,950 →
4,008 → 2,224 while leaving `me` at 543 — consistent with the root cause being
a parser/HIR receiver-naming mismatch, not an import-resolution defect.

### Repro

```bash
sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy
# stage-4 log: build/bootstrap/logs/<triple>/stage4-native-build.log
grep -c 'unresolved name: me' <stage4 log>
```

Faster: run the stage-4 native-build command directly with a stage3 binary
(see `bootstrap_native_build_main` in `scripts/bootstrap/bootstrap-from-scratch.sh`),
adding `SIMPLE_BOOTSTRAP_DIAG=1`.

## Related

- `stage4_focused_subbuild_star_import_unresolved_2026-07-27.md` — the other
  remaining stage-4 blocker (module-key canonicalization for the lexer family)
- `doc/03_plan/agent_tasks/simple_riscv_hardening_2026-07-27.md` (Lane H)
- `native_me_receiver_no_mutate` — duplicate-receiver defect site referenced
  by the fix's non-regression argument
