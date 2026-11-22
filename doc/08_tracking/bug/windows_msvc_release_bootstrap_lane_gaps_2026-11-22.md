# Windows MSVC release bootstrap: lane gaps hit on `release/1.0.0` (2026-11-22)

Host: DESKTOP-VMF96U6 (Hyper-V dynamic-memory guest, 24 CPU, 64 GiB), Git Bash,
`--msvc`, LLVM 23.1.1 MSVC prefix. First found on `release/1.0.0` @ `f207083733f`
(its two Stage 2 compile errors were already fixed upstream by the time of
`a20233fd230`, under `stage2_if_val_struct_option_binding_as_int_wide_2026-11-03`);
the fixes below are applied on `a20233fd230`.

Goal graph: Phase 2 -> {Phase 3, Phase 4} in parallel, then Phase 3 -> {Phase 3,
Phase 4} in parallel. Each item below blocked an edge; workarounds are scoped
to the launcher unless noted.

## 1. Default GNU lane has no usable LLVM 23 on this host (open)

`platform-detect.shs` needs `<prefix>/lib/libLLVM-23.dll.a`; only MSYS2 CLANG64
LLVM 22 and an import-less llvm-mingw exist. Workaround: `--msvc`.

## 2. Start guard refuses on the ballooned guest (#8931, Stage 3 gap fixed here)

`SIMPLE_BUILD_MEMORY_RESERVE_BYTES` reaches the Stage 2 sanity child
(`bootstrap-from-scratch.sh:2511-2618`) but NOT the Stage 3 resume child: its
`env -i` vector is rebuilt from the Stage 2 transcript allowlist, `HOME` is
sandboxed (so `~/.config/simple/host.sdn` `mem_reserve_free_mib` is invisible),
and no hostname variable is passed (so `config/host/<hostname>.sdn` is
invisible). Probed: hello-world under that env with a tracked
`mem_reserve_free_mib: 2048` still reports the 24576 MiB reserve.

Measured: touching and freeing 26 GiB from PowerShell raised
`\Memory\Available MBytes` 15188 -> 26656 and it held ~27 GB for 5+ minutes, so
the memory is real; the guard reads the balloon. Workaround used: that
allocation probe immediately before launching Stage 3. Fixed here: `resume-stage3-from-admitted.sh` forwards a validated
`SIMPLE_BUILD_MEMORY_RESERVE_BYTES` through the worker `mc_env` slot (so it is in
the args hash and the `env -i` vector) and `manifest-verify.shs` reconstructs it
from the transcript; absence keeps the previous vector byte-for-byte.

## 3. In-bootstrap planner smoke reported `planner-smoke-accepted-untyped-reason` (open)

`--produce-stage3-receipt` aborted the Stage 2 run at 02:30. The produced
`planner.exe` run standalone with `--bootstrap-reason=none` exits 2
(`typed-reason-required`), and the same producer run in the MSVC env passes
(`smoke_rc=2`) and publishes both receipts. Root cause of the in-run zero exit
not found. Receipts were produced out of band with the unchanged producer:

    produce-bootstrap-planner-admission-v2.shs --target=//bootstrap:stage3 \
      --reason=verify-landed-compiler-fix --planner-backend=llvm \
      --parent-compiler=<output>/stage2/x86_64-pc-windows-msvc/simple.exe \
      --bootstrap-output=<output> --out=<output>/stage3-planner-admission.receipt
    (same with --target=//bootstrap:stage4 --reason=self-host-convergence-check
     --out=<output>/managed-stage4-planner-admission-v2.env)

## 4. Admitted resumes exec before Windows materialized startup (open)

`--resume-stage3-from-admitted` execs at `bootstrap-from-scratch.sh:1022`, before
`bootstrap_materialized_startup` at `:1500`, so
`SIMPLE_WINDOWS_MATERIALIZED_LINKS_RECEIPT` is never set and the preflight
git-state binding is recomputed in plain mode (`dirty_fingerprint` mismatch ->
"lacks current authoritative preflight evidence"). Workaround: export the Stage 2
run's verified receipt (`materialized-links/windows-materialized-links.<pid>.env`).

## 5. Tool authority depends on PATH spelling (open)

Sourcing `windows-msvc-bootstrap-env.shs` in the launcher re-spelled
`lld-link` -> `lld-link.exe` and `llvm-config` `/c/` -> `C:/` (same SHA-256), and
the Stage 3 resume refused "Stage-2 tool authority changed since admission".
Workaround: export only `LIB`/`INCLUDE`, exactly as `bootstrap-from-scratch.sh:1573`.

## 6. `admit-built-stage2-compiler-tests.shs` keeps the bare `simple` name (fixed here)

`[ -f "$compiler" ] || compiler="$compiler.exe"` - MSYS `[ -f simple ]` is true
when only `simple.exe` exists, so the admission `candidate_path` never matched
(`phase2-runtime-binding: admission compiler path mismatch`). Fixed to prefer
the `.exe` spelling. The standalone lane also needs `LLVM_SYS_231_PREFIX` and the
LLVM 23 bin on PATH (otherwise MSYS2 `mingw64/bin/clang-cl.exe` is selected and
fails to load).

## 7. MIR shard resume hard-fails on a ledger with no inventory (fixed here)

A Stage 3 attempt killed by the tree RSS cap (6.5 GiB default, 6.76 GiB peak
commit) before MIR left `hir/mir-run-latest` pointing at a queue holding only
`run-key`. The next run's key matched, so `run_mir_shards_resume_v1`
(`src/app/cli/native_build_main.spl:1615`) called
`native_mir_shard_resume_adopt_v1`, which reported "prior inventory unreadable",
and the function returned `fail` -> "MIR shard aggregate failure". Fixed here: that exact
reason (adopt has written nothing yet) now repoints `mir-run-latest` and runs a
full pass like a key mismatch; later adopt failures still fail closed.
The cap itself was raised with `SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB=20971520`.

## 8. Managed resume requires the Phase 2 matrix before Phase 3/4 (by design)

`--resume-managed-from-admitted` refuses without
`stage2-compiler-tests/<platform>/stage2-compiler-tests.env`, so it serializes
the matrix before both phases. The parallel edge was run as two lanes instead:
canonical Stage 3 resume + `admit-built-stage2-compiler-tests.shs`.

## 9. Planner build aborts when the per-file pool cannot admit two workers (fixed here)

Since `e9bb5e9` the planner admission build defaults to the per-file pool. On
the ballooned guest (4.7 GB reported free) it logged `per-file worker pool
refused (hir_workers=0 mir_workers=0, need >= 2)` and `MIR shard aggregate
failure`, yet `native-build` exited 0 with no executable, so the producer's
llc-noop retry never ran and the Stage 2 run aborted with
`planner-build-produced-no-executable`. Fixed here: that signature retries once
on the phase route (`SIMPLE_FILE_WORKERS=0`). Still open: `native-build` must not
exit 0 after a MIR shard aggregate failure that produced no artifact.

## 10. Memory pressure source on this host (not a compiler leak)

With only Stage 2 sanity running, processes held ~7 GB while `\Memory\Cache Bytes`
was 44.6 GB and the Everything indexer 6.8 GB private. The repo had 343 git
worktrees (each a ~150k-file checkout) plus one pinned bootstrap snapshot per
attempt under `build/bootstrap/pinned-src/`; NTFS metadata for that file count
stays in the active system cache. Pinned snapshots are never collected, so every
restart adds another 151k files. Mitigation: merged worktrees pruned.

## 11. Tool authority bound a transient `--version` exec status (W11, fixed here)

`bootstrap_stage3_tool_authority_snapshot` (`scripts/check/lib/bootstrap-stage3/authority.shs`)
recorded the raw `env -i … <tool> --version` status as `version-status=` in
`tool-authority-*.txt`, which the Stage 3 resume compares with `cmp -s`. Under
memory pressure the same `lld-link` (same sha256, same version text) returned 125
on 4 of 5 resume attempts and the resume refused "Stage-2 tool authority changed
since admission". Fixed: the probe is `bootstrap_stage3_tool_version_probe`, which
on Windows hosts retries only env(1)'s exec-failure class (125/126/127) up to 5
times with a 1..4 s backoff and a stderr note per retry. Any other status (BSD
`--version` exits 1) is a stable binding and is never retried; a failure that
outlasts the bound is recorded as-is, so an unrunnable or different tool still
mismatches. The line format is unchanged. Linux/macOS/FreeBSD keep a single
probe. Test: `scripts/check/bootstrap-stage3-tool-version-probe-test.shs`
(reproduction: 125 twice then success binds 0; generalization: 126/127, a
persistent 125 bounded and kept, BSD status 1 not retried, single-attempt hosts
unchanged).

## 12. Stage 2 admit lane stayed alive after `REJECTED` (W12, fixed here)

`admit-built-stage2-compiler-tests.shs` printed `admit-stage2: REJECTED` at
11:14:44 and its launcher never logged `EXIT` until an operator killed the lane
tree about 9 minutes later; nothing wrote to the verification directory in
between. The script has no command after the verdict but `exit 1`, and the
verifier waits for its own row jobs, so **the exact process that kept the lane
alive was not identified** (no process listing was captured). Without containment,
anything the verifier left behind survived the verdict. Fixed structurally: the
verifier leads its own process group (perl `setpgrp`, pgid recorded beside the
receipt), the logged subshell runs in the background behind `wait` so signal
traps fire, and after the verdict and on HUP/INT/TERM the lane TERMs that group,
waits up to 10 s, then KILLs it. Trade-off: the verifier is no longer in the
launcher's process group, so `kill -9` of the admit shell itself (no trap)
orphans it where a launcher group kill used to reach it; a Windows tree kill
(`taskkill /T`) still does. Test:
`scripts/check/admit-stage2-compiler-tests-lane-test.shs` (reproduction: a stub
verifier that leaves `sleep 300 &` and exits 1 — the pre-fix script leaves it
alive, `FAIL — orphan: verifier child survived the verdict`; generalization: TERM
to a lane blocked in the verifier exits 143 and reaps it).

## 13. Standalone admit lane did not inherit the wrapper's toolchain env (W13, fixed here)

Run outside `bootstrap-windows.sh`, the admit lane needed `SIMPLE_LINKER_FLAVOR=msvc`,
`LLVM_SYS_231_PREFIX` and LLVM 23's `bin` ahead of MSYS2 mingw64 (whose
`clang-cl.exe` fails to load) exported by hand. Fixed:
`scripts/bootstrap/lib/admit-stage2-toolchain-env.shs` derives the ABI from
`--platform`, keeps an environment value and refuses one that contradicts the
triple (exit 64, before any earlier rejection is superseded), and on MSVC
resolves the prefix from `LLVM_SYS_231_PREFIX`, `SIMPLE_LLVM_WIN_ROOT_23`, the
host config `llvm_root` (as `platform-detect.shs`), then the pinned locations
`windows-msvc-bootstrap-env.shs` knows, requiring `clang-cl.exe` and
`lld-link.exe` and putting its `bin` first unless `clang-cl.exe` already
resolves there. `LIB`/`INCLUDE` are still the caller's (not derived here). It is
sourced from the admit script's own directory, so older source roots work.
Tests: same lane test (8 helper cases and a conflicting-flavor lane run that
exits 64 with the prior `rejection.env` untouched).

## 14. Killed resume left `bootstrap.lock` that blocked every later run (W14, fixed here)

`resume-stage3-from-admitted.sh` took `<output>.lock` with a bare `mkdir`; a run
killed outright never ran its trap, and every later run refused "bootstrap
output is locked" until the operator verified pid 16803 dead and moved the lock
aside. Fixed: `scripts/bootstrap/lib/output-lock.shs` records the pid and, on
Windows, `/proc/$$/winpid`. A held lock is recovered only when liveness is
`dead`: `kill -0` fails and the process table was read without finding the pid
(`tasklist` by Win32 pid on MSYS, `ps -p` elsewhere). `alive` or `unknown` (no or
malformed pid, a pre-fix lock with no Win32 pid, a failed `tasklist`) keeps the
refusal. A lock that the trap deliberately retained (Stage 3 descendants not
proven stopped) now carries a `retained` marker and is never recovered. The
stale lock is moved aside as `<lock>.stale-pid<pid>-<stamp>-<$$>`, re-checked after
the move, and never deleted. Known limit: owner death does not prove that a
SIGKILLed owner's descendants stopped. `check-stage3-recovery-authority.shs`
still reports `stale-output-lock` as refused. Test:
`scripts/check/bootstrap-output-lock-stale-test.shs` (reproduction: dead owner
recovered with the evidence kept; generalization: live owner, retained, garbage
pid, missing Win32 pid, and failing `tasklist` all refused).
