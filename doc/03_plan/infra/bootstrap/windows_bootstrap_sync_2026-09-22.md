# Windows bootstrap integration — 2026-09-22

## Source selection

Isolated repository: `D:/b-sync`, local branch `main`. GitHub main fetched with
jj is `e0dd873da1b7828389db4eb60e82972cc8245313`. Rebase of the existing
`2984a5ff` candidate onto `main@origin` was a no-op: all commits were already
based on that main. Tracked count stayed 137438 before/after rebase.

Selected PR commits, in order after the four existing #1265 fixes:

- `b737ea72`: #1265 restart handoff documentation.
- `77fb2dd0`: native Windows authority compatibility link; avoids MSYS copy emulation.
- `7b23ad03`: #1254 bounded Cargo child cleanup after root exit.
- `4e2bd871`: #1284 unknown status for incomplete process observations.

The last three implementation changes were reviewed independently of their
stacked PR ancestry. #1253 and the LLVM-C import change `21407c7` were excluded:
they require the LLVM23 seed migration, while this lane preserves LLVM18 seed
bindings and pins only the native C frontend to clang-cl23. #1217 performance
and #1285 concurrency changes were also excluded from this blocker integration.

SPipe remains initialized at `155d58a4898750bf9e20f8f1d656ad8185111687`.
Cherry-picks added exactly two tracked files (137440 total before this report).
Nothing was pushed to GitHub; the original shared checkout was not rebased.

## Focused verification

- Native compatibility-link regression: PASS on Windows.
- Windows bounded collector regression: PASS, 14 actual cases; evidence under
  `build/native_probe/stage2-sanity-windows/collector-regression-wosd5xqb`.
- Watcher check: WARN, 24 of 25 checks passed with the canonical MSYS shell.
  Fixed fixture startup accounting to measure idle CPU delta and added cleanup
  of CPU-loop children. Remaining assertion assumes the CPU worker `awk` has
  largest RSS; Windows reports `sh`. Production selects largest RSS, so this
  assertion does not prove a production failure. Full check is not claimed PASS.
  Evidence: `build/watcher-check-review-msys.log`.

## Bootstrap handoff

Astra owns the existing run in `D:/wk-br2984-lfs` (session 15924). Its source
and cache remain separate from this candidate. Transition only after its Cargo
writers finish, or its process reaches a terminal state. The integrated build
uses private output `build/bootstrap-sync-20260922`, no-stub fallback, the
original MSVC setup, clang-cl23, 12 jobs, LLVM backend and dynload mode.

The original post-Cargo fingerprint failure is not proven fixed by these PRs:
an isolated replay passed with the original digest. Retain its evidence and
require actual Stage2 admission before Phase2 tests or Stage3. Materialization,
Rust build completion, and focused test passes are not Stage2 admission.
