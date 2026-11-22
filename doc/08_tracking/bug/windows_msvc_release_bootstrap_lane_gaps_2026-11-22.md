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
