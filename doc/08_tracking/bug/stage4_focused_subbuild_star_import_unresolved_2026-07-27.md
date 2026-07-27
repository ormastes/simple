---
id: stage4_focused_subbuild_star_import_unresolved_2026-07-27
status: open
severity: high
discovered: 2026-07-27
discovered_by: full-bootstrap --deploy run from current origin main (Stage 4, full-CLI focused sub-builds)
related: src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl
related: scripts/bootstrap/bootstrap-from-scratch.sh
---

# Stage 4 focused sub-builds fail star-import resolution; bootstrap deploy blocked

**Status:** open — bootstrap deploy did not occur; `bin/simple` still resolves to
the 2026-07-25 Rust seed (`bin/release/x86_64-unknown-linux-gnu/simple`, mtime
2026-07-25 05:30:43, size 145290352).

## Summary

Stage 4 of `--full-bootstrap --deploy` now lowers all 1,752 HIR modules with
**zero segfaults** (the prior deterministic segfault at HIR module 32 is fixed —
see `doc/03_plan/agent_tasks/simple_riscv_hardening_2026-07-27.md` §6, commit
`9b612a11418c`). It then fails with **6,144 errors**, all inside `focused
native-build` sub-builds:

- 5,950 `unresolved name: X`
- 166 `untyped function returns a value`

Deploy never happens because the focused-build phase does not reach a green
state.

## Symbol histogram (top offenders)

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

## Proof this is pre-existing, independent of today's HIR-segfault fix

The same failure class was measured earlier today (2026-07-27) on a **different
tree** (159 commits older) with a **different compiler build**:

| Run | Tree | Total errors | `MirType` | `me` | `mir_operand_copy` |
|---|---|---|---|---|---|
| Earlier (pre-HIR-fix) | 159 commits older | 11,826 | 913 | 543 | 490 |
| Today (post-HIR-fix) | current origin main | 5,950 (+166 untyped-return = 6,144) | 760 | 543 | 393 |

The `me` count is **byte-identical (543) across both runs** — strong evidence
this class of failure has a fixed, deterministic cause unrelated to the HIR
segfault fix that landed between the two runs. The other counts roughly halved,
consistent with the HIR fix removing one contributing factor (likely a
subset of modules that previously never reached this phase) without touching
the star-import resolution defect itself.

## Control probe (PASSED) — implicates focused-build closure, not star-import handling in general

A small entry-closure build (`--source src/compiler --entry-closure`) of a file
containing `use compiler.mir.mir_data.*` and using `MirType` **compiled and ran
cleanly** earlier today. So star imports resolve correctly when the imported
module is inside the build closure. This points at the **focused sub-build's
closure computation** — imported modules reachable only via a star import are
apparently missing from the per-focus closure — rather than at star-import
resolution itself being broken.

## Hypothesis

Each `focused native-build` sub-build computes its own module closure (files it
will parse/lower/codegen for that focus). The hypothesis is that this closure
computation does not follow star imports (`use X.*`) the same way the
whole-source / entry-closure build does, so modules like `compiler.mir.mir_data`
(providing `MirType`, `MirTypeKind`, `MirConstValue`, `MirOperand`, …) and
`compiler.lex.token` (`TokenKind`, `lex_make_token`) never get added to
`modules_by_name` for the affected focus, and every star-imported name from
them resolves as unknown.

## Sub-defect: `me` as an unresolved name (543 occurrences, both runs)

`me` is the method-receiver keyword, not an importable symbol — it should never
appear as an "unresolved name" target at all. Its count is **byte-identical
(543)** across two different trees/builds, which suggests a single
deterministic site (or small fixed set of sites) that misidentifies `me` as a
name lookup instead of the receiver keyword, most likely inside method bodies
that live in files affected by the star-import closure gap above (once the
containing method's imports fail to resolve, something in error recovery or a
downstream check may re-report `me` itself as unresolved). This is called out
separately because it does not obviously reduce with the star-import fix and
should be verified independently once the closure gap is fixed.

## Reproduce

```sh
sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy
```

Run from a worktree at current `main`. Stage 4 log:
`build/bootstrap/logs/x86_64-unknown-linux-gnu/stage4-native-build.log`
(evidence for this run; job path
`/home/ormastes/.claude/jobs/4403a7d8/tmp/wt-bootstrap/build/bootstrap/logs/x86_64-unknown-linux-gnu/stage4-native-build.log`).

## Impact

Bootstrap deploy is blocked at Stage 4 for the full-CLI focused-build path.
`bin/simple` remains the 2026-07-25 Rust seed. Every gate that requires the
redeployed self-hosted binary (RISC-V hardening campaign gates, and any other
consumer of `bin/simple`) stays seed-attributed until this is fixed.

## Suggested next diagnostics

1. Re-run Stage 4 with `SIMPLE_BOOTSTRAP_DIAG=1` and grep the log for
   `[import-miss]` (or the closest equivalent diagnostic marker emitted by the
   focused-build closure/import-resolution path) to confirm directly whether
   star-imported modules such as `compiler.mir.mir_data` and
   `compiler.lex.token` are **absent** from the focused sub-build's
   `modules_by_name` (closure-computation bug) versus **present but
   unregistered** (a registration/lookup bug closer to the recently-fixed
   `Dict.get()`/`Dict.len()` native defects — see
   `doc/08_tracking/bug/native_dict_get_struct_value_corrupt_option_2026-07-27.md`
   and `doc/08_tracking/bug/native_dict_len_returns_minus_one_2026-07-27.md`).
2. Compare the focused-build closure-computation code path against the
   entry-closure path that the control probe used successfully, specifically
   for how each follows `use X.*` star imports when building the module set.
3. Once the closure gap is understood, separately verify whether the `me`
   sub-defect (543, both runs) persists — if it drops to zero once star-import
   resolution is fixed, it was a downstream symptom; if not, it needs its own
   fix.
