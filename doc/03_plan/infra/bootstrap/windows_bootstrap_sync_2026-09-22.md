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

## Final bounded-session handoff

The old run was intentionally stopped after its Cargo writers finished. Three
integrated full runs were executed in this private output; no fourth run is
authorized in this session. All retained Rust/native caches remain intact.

| Integrated source | Terminal result | Proven progress / first failure |
| --- | --- | --- |
| `cfb58af2b0afc2aeafa4e58a7f7be5ed2aa5cde6` | exit 1 | Rust seed/runtime completed; Windows source consumer rejected pinned gitlink |
| `e232e7657beac1d56611bb32cf3017861da988ae` | exit 2 | Stage2 900 compiled, 0 failed; frontend collector waited after native exit 0 |
| `392a899c0b7269637ca70c46f239d623b3078799` | exit 3 | Stage2 2 compiled, 898 cached, 0 failed; all eight frontend probes passed; receiver rejected MSYS-converted CL |

Intervening reviewed fixes added pinned-gitlink auditing, literal bracket paths,
bounded 400000 cumulative entries, exact MSYS/native gitlink-root mapping, and
strict owner-bound generated bootstrap symlink admission. The real-tree source
consumer passed at e232 with a fresh current-HEAD materializer receipt. Leaf
`737cd92020562a8213c150d77fc93c990c4dd773` was then cherry-picked as 392a899:
Windows synchronous frontend probes select scoped job cleanup after root exit
and attest that policy. Policy regression and 14 actual Windows collector cases
passed; a fresh positional hello-world build/run proved native/raw exit 0 and
stdout `hello`, with the leftover process identified as `vctip.exe`.

Final full-run interval: `2026-09-22T12:18:15Z` to
`2026-09-22T12:28:11Z` (596 seconds), owned session 30133. Native observed peak
aggregate RSS was 1,310,560,256 bytes; terminal free D: was 58,286,063,616 bytes.
Stage2 compile/link took 49.4 seconds. The current sanity receipt is `status=pass`
with both bootstrap modes passing all eight bounded frontend probes. The outer
failure diagnostic quoted an old frontend timeout log; the current first real
failure is in `stage2-receiver.log`, not that stale sibling log.

The receiver inherited `CL=/TC`, which MSYS transported to native clang-cl as
`C:/dev/tool/Git/TC`. The reviewed Windows-only setup fix idempotently adds `CL`
to `MSYS2_ENV_CONV_EXCL`, preserving existing exclusions and ordinary path
conversion. It does not discard compiler options or disable conversion globally.

Focused verification after the final full run:

- Native environment regression PASS: literal `/TC`, existing exclusions,
  repeated-source idempotence, and unrelated POSIX-path conversion.
- Actual receiver probe PASS, session 83517, UTC 12:31:47–12:32:25:
  `bootstrap_stage2_struct_receiver=PASS` and
  `bootstrap_stage2_positional_stage3_route=PASS`.
- Tested candidate SHA-256, unchanged before/after:
  `a814dda186e55fec840027278c5e4be1b0395b3174fca172a28b045996479171`.
- Tested candidate remains rejected at
  `build/bootstrap-sync-20260922/stage2-rejected/x86_64-pc-windows-msvc/simple.exe`;
  its `rejection.env` is retained. Focused PASS does not promote it.

Evidence beneath `build/bootstrap-sync-20260922/`: `evidence-cfb58af-run1/`,
`evidence-e232-run2/`, `console-392.log`, `resources-392.log`,
`stage3/x86_64-pc-windows-msvc/stage2-sanity.env`, `stage2-receiver.env` and
`stage2-receiver.log` in that same directory, `receiver-cl-fix/console.log`, and
`windows-msvc-cl-environment-test.log`. No cache was deleted and no changes were
pushed. Materialized-alias working-tree differences were not committed.

### Next canonical verification — new authorization required

**Stage2 admission is still incomplete.** Stop here for this session. In a fresh
bounded session, main must authorize and schedule the following command on the
new committed HEAD in `D:/b-sync`, after archiving current evidence and checking
the pinned SPipe, disk floor, and absence of other cache writers. Do not rerun
the previously passing focused tests or use `launch-392.sh`, whose HEAD guard
intentionally binds the old candidate.

```sh
source scripts/setup/windows-msvc-bootstrap-env.shs &&
export CC="C:/dev/tool/clang+llvm-23.1.1-x86_64-pc-windows-msvc/bin/clang-cl.exe" &&
export CXX="$CC" CL=/TC SIMPLE_LINKER_FLAVOR=msvc SIMPLE_NO_STUB_FALLBACK=1 &&
export SIMPLE_LLVM_BIN="C:/dev/tool/clang+llvm-23.1.1-x86_64-pc-windows-msvc/bin" &&
sh scripts/bootstrap/bootstrap-windows.sh --msvc --full-bootstrap --stop-after-stage2 --backend=llvm --mode=dynload --jobs=12 --output=build/bootstrap-sync-20260922 --progress=build/bootstrap-sync-20260922/progress.log
```

Require fresh current-HEAD materialization and canonical Stage2 admission;
retain all fingerprint controls and producer-bound caches. Only afterward may
main assess external Phase2 verifier adoption from prepared
`D:/b-phase2` HEAD `99400f03fa17c7681196761587343e217bbcaee5` against the actual
admission bindings. No Phase2 or Stage3 execution was performed in this lane.
