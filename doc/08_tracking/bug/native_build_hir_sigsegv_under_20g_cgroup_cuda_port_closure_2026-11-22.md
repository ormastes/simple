# native-build worker SIGSEGVs at HIR 82/514 only under a 20 GiB cgroup (CUDA port closure)

- **Date:** 2026-11-22
- **Status:** open
- **Severity:** P2. Blocks the end-to-end native link of the CUDA backend port
  closure, and with it the verification of `cuda_optimizer_surface_owner_2026_10_10`
  and `cuda_port_imported_method_surface_type_owner_2026_10_16`.
- **Found by:** lane `work/cuda-compiler-bugs`.

## Repro

- **Producer:** integ25 Stage 2 admitted native-build
  (`build/bootstrap-s2probe-integ25/stage3/aarch64-unknown-linux-gnu/stage2-admitted/simple`
  under the integ5 pinned-src tree), sha256
  `ef46f0d2ab4274c4550530851db407bf9bad7f21bfabd50f9b56e87e77fd58d6`.
- **Runtime:** sibling `stage2-runtime-authority`.
- **Host:** Linux aarch64 (NVIDIA GB10). Source base `release/1.0.0` `3c2e4556b6d`
  plus the owner-import removal.

```
SIMPLE_BOOTSTRAP=1 SIMPLE_NATIVE_GO_TO_END=1 SIMPLE_FILE_WORKERS=0 SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1 \
  systemd-run --user --scope -q -p MemoryMax=20G -p MemorySwapMax=0 <stage2> native-build \
  --source src/compiler --source src/app --source src/lib --source src/plugins/backend_cuda \
  --source src/compositions/kernel_llvm_cranelift --source test/native/cuda_compiler_bugs/port_owner \
  --entry-closure --entry test/native/cuda_compiler_bugs/port_owner/main.spl \
  --runtime-path <stage2-runtime-authority> --cache-dir <fresh> --output <out>
```

## Observed

| cgroup / config | result | peak RSS (`/usr/bin/time -v`) |
|---|---|---|
| 20G, default threads (HIR worker pool sized to 1) | `native-build worker terminated with signal 11 (SIGSEGV)`, worker exit -139, build rc 117, at HIR 82/514 | 4.01 GB |
| 20G, `--threads 1` | same, HIR 82/514 | 4.01 GB |
| 20G, `SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB=8388608` (HIR in-process, `[shard] threads=0`) | same, HIR 82/514 | 4.01 GB |
| 8G, unchanged (control, run twice) | passes HIR 82; one run completed HIR 514/514 | n/a |

- Only the cgroup `memory.max` differs between the crashing and passing runs,
  and peak RSS is far below either cap. So this is a compiler crash that depends
  on the cgroup limit, not memory pressure.
- In the 20G runs the HIR module order diverges right after
  `lib.nogc_sync_mut.io.process_ops`: the next module is
  `compiler.mir_opt.perf_facts` instead of `lib.nogc_sync_mut.sffi.runtime`, and
  the crash follows.
- **Candidate:** code that sizes or orders work from `shard_cgroup_memory_max_kb()`
  (`src/app/cli/shard_mem_clamp.spl`) or reads the cgroup limit elsewhere. Not yet
  bisected.

## Crash artifact

Crash report file:
`/var/crash/_home_yoon_dev_simple-integ5-20261116_build_bootstrap_pinned-src_pinned-c1a10190b978_build_bootstrap-s2probe-integ25_stage3_aarch64-unknown-linux-gnu_stage2-admitted_simple.1000.crash`.
It was written by the 20G runs. Get a backtrace from it before it rotates.

## Next step
1. Take a backtrace from the crash file.
2. Find what reads `memory.max` and changes HIR scheduling.
3. Make HIR order and memory sizing independent of the cap, or fix the crash
   directly.
