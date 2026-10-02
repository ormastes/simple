# Collection selector bound regression: test-first evidence

Status: **BLOCKED — no executable RED or GREEN**. This is selector validation,
not proof of production CollectionPlan extraction, lowering, or execution.

## Ownership and sequence

- Owner: `/root/item3_planner`; session `01a0fedc-f802-7af2-ab5b-a5c6abe85984`.
- Worktree: `C:/dev/simple-item3-planner-20261003`.
- Branch: `work/item3-planner-20261003`; target: `release/1.0`.
- Base and observed target: `cb2f783acf0ea22e8da54ff0d8d18b4fb14c816c`.
- Tests committed before source: `944e1fe7644`.
- Source guard committed after diagnostic build attempts: `8ab6c4d7bd1`.
- Review added static-only coverage, independent of profile admission.

The unit tests cover all four policies and all four attributes for static and
admitted-profile contradictions, exact/zero boundaries, and stale unadmitted
profiles. The standalone native probe imports the real production selector.
The fix rejects inconsistent upper-bound evidence before any candidate is
selected and reports `contradictory-size-bound`; unknown bounds remain unknown.

## Diagnostic runtime identity and command

The parent identified this pure-Simple bootstrap binary (not Rust seed):
`C:/Users/user/.simple/worktrees/simple-windows-phase2/build/bootstrap-llvm80/stage2/x86_64-pc-windows-msvc/simple.exe`.
Its reported version is `simple-bootstrap 1.0.0-rc.1`. Its lineage is
**unadmitted**, and it exposes compilation rather than the required full
`test`/`check` CLI. These attempts cannot satisfy release verification.

From the owned worktree, the exact arguments were:

```text
native-build --source src/compiler --entry-closure --backend llvm --target x86_64-pc-windows-msvc --runtime-bundle core-c-bootstrap --runtime-path C:/Users/user/.simple/worktrees/simple-windows-phase2/build/bootstrap-llvm80/stage3/x86_64-pc-windows-msvc/stage2-runtime-authority --threads 2 --entry test/02_integration/compiler/collection_plan_bound_native_probe.spl --output build/item3-planner-tdd/collection_plan_bound_native_probe.exe
```

Both attempts set `SIMPLE_NO_STUB_FALLBACK=1` and `SIMPLE_CACHE_DIR` to the
owned worktree's `build/item3-planner-tdd/cache`. PowerShell `Start-Process`
used a hidden window, redirected both streams, and bounded `WaitForExit` to
120000 milliseconds; timeout stops only that owned process.

1. Initial attempt exited 1 before compilation with
   `SCV-E-ADMISSION: compile-event-journal-missing`, requesting the first-build
   cold inventory flag. Logs: `build/item3-planner-tdd/red-build.stdout.log`
   and `red-build.stderr.log`.
2. The single retry additionally set `SIMPLE_SCV_INVENTORY_COLD_INIT=1`.
   It timed out after 120 seconds and was stopped. Logs:
   `build/item3-planner-tdd/red-cold-build.stdout.log` and
   `red-cold-build.stderr.log`. Only the workaround-coverage note was emitted;
   no compiler diagnostic or assertion result was produced.

After timeout, process inspection found no remaining matching native probe
process, and `Test-Path build/item3-planner-tdd/collection_plan_bound_native_probe.exe`
returned `False`. The diagnostic process is terminal; this is not an observed
failing regression assertion. No GREEN attempt was made because the compiler
blocker remains unchanged. `git diff --check` passed for the authored delta.

## Remaining gates

Run the unit spec and native probe with an admitted self-hosted runtime,
demonstrate the expected failing assertion at the test-first commit and passing
assertions with the fix, then run compiler/core/MCP and environment guards
required by AGENTS.md. Production planner invocation and executed MIR,
cross-engine semantic parity, profiling, memory, and performance acceptance
remain outstanding. This report does not authorize release or a PASS claim.

## Read-only timeout diagnosis (2026-10-03 addendum)

The earlier `SIMPLE_CACHE_DIR` setting had **no effect on this native-build
route**. `src/app/io/_CliCompile/native_build.spl:437` defaults native artifacts
to the worktree-local `build/native_cache`; `--cache-dir` is the supported
override. `native_build_main.spl:356` also derives the frontend cache from that
explicit flag. SCV admission independently fixes its cache at
`<checkout>/build/scv` (`compile_source_inventory_core.spl:227`). Thus the prior
environment assignment must not be interpreted as verified cache isolation.

`compiler_source_authority_acquire_v1` expands a cold inventory to **both
complete `src` and `test` families**, even with `--source src/compiler` and
`--entry-closure` (`source_authority.spl:103`). Inventory refresh precedes source
snapshot construction and entry closure. Cold refresh lists tracked and
untracked paths, filters to admitted sources, then reads/hashes each source
(`inventory_events.spl:311`). The Git subprocess timeout is 300 seconds
(`inventory_events.spl:134`), longer than the diagnostic's 120-second outer
limit. The existing Windows cold-inventory bug report documents the substantial
enumeration cost, but does not measure this specific attempt.

Post-attempt inspection found only `build/scv/compile-events/refresh.lock`
(zero bytes); no inventory pointer, event cursor, or snapshot had been
published. This locates the interruption **before inventory publication**;
there is insufficient evidence to distinguish lock acquisition, Git listing,
source hashing, or inventory assembly. No exact hotspot is claimed.

The Windows runtime lock uses `CreateFileA(OPEN_ALWAYS)` plus `LockFileEx`,
and unlock closes its handle (`src/runtime/platform/platform_win.h:307` and
`src/runtime/runtime_host_file_exports.c:95`). The file's continued existence
does not indicate an active lock. The prior process is terminal; no lock-file
deletion, cache deletion, copied admission receipt, or admission bypass is
needed for a later authorized attempt.

A materially different final diagnostic attempt could keep the same admitted
source path but add `--cache-dir build/item3-planner-tdd/native-cache --timeout
90`, retain `SIMPLE_SCV_INVENTORY_COLD_INIT=1` and strict no-stub mode, and allow
a **360-second total outer budget**, observed in intervals no longer than 60
seconds. That budget can outlive a single 300-second inner Git timeout, but
does not guarantee that full cold admission finishes: hashing has no matching
total deadline. `--timeout 90` controls the later worker, not parent admission.
On a fixed head, even a successful probe would be diagnostic GREEN only;
observing RED requires an explicitly owned pre-fix source state corresponding
to `944e1fe7644`.

## Final authorized diagnostic outcome

The parent authorized exactly one final attempt with that larger bounded
budget. Only the owned selector file was temporarily restored from the
test-first commit `944e1fe7644`; both its tree blob and working-file hash were
`99e74bd2243ea1a7e6faab6ca5f349c7c6c23308`. The current native probe remained
unchanged and its first assertion required the contradiction to select Original.

The command above gained `--cache-dir build/item3-planner-tdd/native-cache
--timeout 90`. `SIMPLE_CACHE_DIR` was removed, while
`SIMPLE_SCV_INVENTORY_COLD_INIT=1` and `SIMPLE_NO_STUB_FALLBACK=1` remained.
No admission receipts or locks were copied, deleted, or bypassed. Logs are
`build/item3-planner-tdd/red-final-build.stdout.log` and
`red-final-build.stderr.log`; the recorded process ID was 28872.

The process remained live and CPU-active, with these parent-process samples:

| Elapsed seconds | CPU seconds | Working set bytes |
|---|---|---|
| 30 | 2.609375 | 35287040 |
| 91 | 61.328125 | 38449152 |
| 150 | 118.9375 | 40960000 |
| 240 | 206.734375 | 44122112 |
| 301 | 266.890625 | 49790976 |
| 330 | 296.03125 | 52486144 |

At 360 seconds the watchdog terminated only the owned process tree: compiler
PID 28872 and its console child PID 30172. The wrapper observed terminal exit
1, and the expected executable was absent. Stderr still contained only the
workaround-coverage note. Post-termination process lookup found neither PID;
SCV still contained only the zero-byte refresh lock and no published inventory.
This is a **cold-inventory timeout**, not a failing selector assertion.
The substantial CPU use after the initial wait supports in-process inventory
work rather than a continuously blocked Git child; the exact hashing/assembly
hotspot remains unmeasured.

After terminal status, the selector was restored from `6437b1e340c`; its tree
blob and working-file hash both matched
`db8e4cbb92795d67372244cf46cb4e556be1820f`. No pre-fix source remains in the
working tree. Three total compile attempts have now exhausted this session's
diagnostic cap. No executable was run and no fourth compile was attempted.
There is still no observed semantic RED, GREEN, admitted runtime evidence,
or release PASS.
