# Three C runtime source lists with no cross-check (2026-09-01)

Status: **GUARDED** — `scripts/check/check-runtime-source-list-parity.shs`, wired as
the `push-runtime-source-list-parity` push gate.

## Defect class

Prevention item **#2** of
`doc/01_research/compiler/why_missing_symbols_do_not_fail_the_build_2026-09-01.md`.
Companion record: `doc/08_tracking/bug/c_runtime_source_list_divergence_2026-08-30.md`.

Three independent rosters decide which `src/runtime/*.c` files get compiled, and
nothing compared them:

| lane | file | function |
|---|---|---|
| `seed`   | `src/compiler_rust/compiler/src/pipeline/native_project/tools.rs` | `build_c_runtime_library` |
| `simple` | `src/compiler/70.backend/backend/runtime_compiler.spl` | `compile_runtime_objects` |
| `rust`   | `src/compiler_rust/runtime/build.rs` | `compile_c_runtime_sources` |

A merge dropped ONE line from ONE list while the `.c` file stayed in the tree
(`d122c1a4b78`: "the file survived, so nothing looked missing") — 18 symbols
lost. `ea30567675` did the same to `runtime_contracts.c`. `runtime_terminal.c`
and `runtime_simd_case.c` sat in one list and not another for months. No diff
review sees this: the deletion is a single string literal, and the tolerated
final link (Q1.1 of the research doc) turns the result into a NULL GOT slot and
a SIGSEGV at first call rather than a build error.

Every existing guard is blind to it. `check-c-runtime-compiles-push.shs` runs
`clang -fsyntax-only` over the TREE, so a file that no list compiles still
parses fine. `check-runtime-api-regression-push.shs` greps for *definitions*, so
a still-present definition that is never compiled looks healthy.
`check-no-unresolved-runtime-symbols.shs` is artifact-scoped and honestly RED.

## The guard

Pure text/shell: no compiler, no built artifact, no `bin/simple` — so it is a
`push` row, which is exactly why this item was ranked "cheapest, catches all of B".

For every owned `*.c` under `src/runtime/` (CLAUDE.md Owned-Code Scope: `vendor/**`
excluded) it computes a MEMBERSHIP SIGNATURE — which lanes compile it, with unity
`#include "x.c"` expanded to a fixed point — and diffs the whole map against
`scripts/check/runtime_source_list_parity_baseline.txt`. Comment lines are
stripped before literals are harvested, because all three lists carry prose that
names files deliberately NOT compiled (`build.rs`: "Do NOT add
startup/baremetal/runtime_log.c to this list").

The baseline IS the explicit, commented per-lane allowlist. Legitimate divergence
is a row, not a special case in code: `hosted_win32.c seed,rust`,
`runtime_sdl2.c simple`, `runtime_terminal.c seed,simple`, and the 81 files with
signature `none` (`test/`, `startup/baremetal/`, `scilib/`, `platform/` — not in
any runtime link).

Fails in BOTH directions, per the ratchet discipline of
`check-unbacked-extern-ratchet.shs`: a changed membership (dropped or unreviewed
new list entry), a new `.c` absent from the baseline, a list entry naming a file
that does not exist (STALE ROSTER), and a baseline row whose file is gone (STALE
BASELINE — a baseline that no longer describes the tree is how a ratchet silently
stops ratcheting). `--generate-baseline` is for reviewed updates only.

`--selftest` runs first, unconditionally, and is fatal: 7 fixtures — clean tree
PASSes; dropped list entry FAILs (the `d122c1a4b78` replay); stale roster FAILs;
new unlisted `.c` FAILs; stale baseline row FAILs; empty tree ERRORs
(non-vacuity); unity `#include` counts as coverage. Every exit status is read
into a variable on the line AFTER the command, never through a pipe.

## Discrimination evidence (real tree, origin/main a6137d15cfc)

Clean:

    PASS — 130 file(s) checked, 0 drift (seed=24 simple=35 rust=24 in-no-list=81)

Incident replay — `"runtime_core_host_services.c",` deleted from `tools.rs`,
the `.c` file left in the tree, exactly as `d122c1a4b78` describes:

    FAIL — 130 file(s) checked, 1 offender(s) (1 changed, 0 new, 0 stale-baseline, 0 stale-roster): runtime_core_host_services.c

## Wiring — and why there is no ledger row

`config/check/must_check_gates.sdn` gains
`push-runtime-source-list-parity, push, true, tree, ...`, and
`scripts/check/check-push-must-pass.shs` gains the matching dispatch case (an id
with no case falls through to `*) return 2`, which would ERROR every push).

**No row is added to `doc/08_tracking/check/must_check_db.sdn`, deliberately.**
The ledger/manifest id-set equality in `check-push-must-pass.shs` builds
`manifest_seen` ONLY from rows matching `, bootstrap,` (`:158`) and then fails on
`manifest_count != ledger_count` (`:191`) and on any ledger id not in
`manifest_seen` (`:195`). The manifest already carries ~12 `push`-tier rows and
the ledger carries none. Adding a `push`-tier ledger row would CREATE the drift
it is meant to prevent.

`sh scripts/check/check-guard-wiring.shs` reports 14 NEW unwired both before and
after this change — i.e. this guard is reached, and the pre-existing 14 are
untouched.
