# `gen-stdlib-api-registry.shs --check` cannot be enforced yet (2026-09-06)

Base: `0dc18e8edfc` (`origin/main`). Host: aarch64 Linux, 20 cores.
Script: `scripts/check/gen-stdlib-api-registry.shs`, landed by `7a4556c1247`.

## What this record is for

`scripts/check/guard_wiring_optout.txt` line 508 opted this script out of
`check-guard-wiring.shs` on the stated ground that it is a **producer with no
pass/fail notion of its own** and that the enforcing gate "does not exist yet".
Both halves of that reason are false, and this record replaces them:

- The script has an explicit `--check` mode (`:343-375`) that emits the repo's
  standard verdict convention as the last stdout line — `PASS — <n> ... ` exit 0
  / `FAIL — ...` exit 1 / `ERROR — nothing was checked (<reason>)` exit 2, with
  zero-checked forced to ERROR — and a `--selftest` with 6 fixtures
  (`PASS — 6 selftest fixture(s) checked`, 0.17s).
- The enforcing gate therefore *does* exist: it is `--check` in this same file.
  It compares the checked-in `config/api/api_registry_stdlib.sdn` shard against a
  fresh scan of `src/lib/<space>` and fails on unregistered or stale rows.

So the script is a **checker with a generator mode**, not a generator. It stays
opted out for the three concrete, measured blockers below — not because it has
nothing to assert.

## Blockers

| # | blocker | measurement on `0dc18e8edfc` | resume command | owner |
|---|---|---|---|---|
| 1 | **RED on main.** `--check` fails: the `sosix` family exports PTY entry points that are in no registry shard. Wiring it blocking would block every push; wiring it advisory would only record a known red. | `FAIL — 2716 stdlib symbol(s) checked in space nogc_async_mut, 7 unregistered, 0 stale; unregistered:nogc_async_mut.sosix.sosix_pty_close sosix_pty_default_shell sosix_pty_is_running sosix_pty_open sosix_pty_read` | regenerate the shard (`sh scripts/check/gen-stdlib-api-registry.shs --space nogc_async_mut --out config/api/api_registry_stdlib.sdn`), review the diff, commit it; then `--check` must PASS | rt_api lane |
| 2 | **No `--rev`/`--ref` mode.** The script reads the working checkout only — `grep -n -- '--rev\|--ref\|git show\|cat-file\|ls-tree'` returns nothing. A manifest row today could only be `mode, tree`, and the 16 existing `tree` rows are mid-migration onto `ref` because they read the wrong tree (the defect that produced a real incident on 2026-09-06). Adding a 17th is a regression. | 0 matches for any committed-content reader | add `--rev <sha>` that materialises `src/lib/<space>` and the shard via `git cat-file`, then add a `push`-tier `ref` row | rt_api lane |
| 3 | **Fork-bound cost: ~4 min wall, and `sys` exceeds `user`.** A push-tier row at this cost drives `--no-verify`, which nullifies every other guard. The kernel-time majority says this is a per-symbol subprocess problem in the scanner, not inherent work — it is a script perf defect, fixable. | `real 3m53.248s / user 4m38.660s / sys 7m51.442s` over 2716 symbols | profile the per-family loop; batch the `grep`/`awk` invocations instead of forking per symbol; target < 30s before proposing any push-tier row | rt_api lane |

Row 1 alone would allow an advisory row; rows 2 and 3 are what make even the
advisory row a net negative today. All three must clear before this script is
proposed for `config/check/must_check_gates.sdn`.

## Not in scope here

The opt-out's remaining observation stands and is not a blocker for the gate
itself: the script also counts **bypass imports** (a file outside a family
importing one of its submodules directly, reaching past `__init__.spl`), and
`doc/01_research/runtime/rt_api/api_surface_classification_2026-09-06.md:475`
records 549 of them. Freezing that population is a separate ratchet with its own
baseline, in the shape of `check-no-direct-rt.shs`; it is not what `--check`
asserts and does not gate this record.

## Sibling

`scripts/check/gen-api-registry.shs` (the `rt` surface twin) is not opted out
only because `check-rt-api-groups.shs` invokes it, so `check-guard-wiring.shs`
already counts it reachable. The stdlib shard has no such consumer.
