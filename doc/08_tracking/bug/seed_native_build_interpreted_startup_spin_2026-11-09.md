# Seed native-build interpreted startup spin — 2026-11-09

Bug id: `seed_native_build_interpreted_startup_spin_2026-11-09`
Severity: P1 · Status: open

## Symptom

The 2026-11-05 Rust seed (`src/compiler_rust/target/bootstrap/simple`,
sha256 `df9dfb057afb7b8f…`, reports `v1.0.0-rc.1`) on an aarch64 20-core host
(`Linux spark-f0ce 6.17.0-1032-nvidia`) never finishes a **cold-cache**
`native-build` of the hello closure: a 2026-11-09 lane observed 45 min at
~98% CPU, RSS 1.6–1.9 GB, build log frozen at 105 KB of frontend diagnostics,
zero cache objects, no binary, no error (see
`build/agent-worktrees/boot-llvm/out/REPORT.md`).

## Repro (diagnosis lane, worktree `build/agent-worktrees/boot-llvmdiagnose` @
`origin/release/1.0.0` `bbe3d42f0e0`)

```
seed native-build --backend <llvm|cranelift> [--entry-closure] --threads 8 \
  --runtime-bundle auto --cache-dir <private-cold-dir> \
  --entry examples/01_getting_started/hello_native.spl -o <out>/hello
```

## Measurements (all with private cold caches, lanes run in parallel)

| Lane | Flags | Result |
|------|-------|--------|
| llvm | `--entry-closure` | killed by 600 s timeout; 99% CPU 1 core; RSS 1.65→1.73 GB then GC dip 1.30 GB; log frozen at 107157 B; 0 cache objects; 0 output |
| cranelift | `--entry-closure` (identical) | identical spin, ≥5 min when sampled |
| cranelift | no `--entry-closure` | identical spin |
| cranelift | 3-line trivial entry, no imports | identical spin; 240 s timeout kill; log frozen at same 107157 B |

Phase timeline (from `SIMPLE_LOG=debug` / `RUST_LOG=info`, span traces):
the seed runs `run_file_with_args{path=src/app/cli/native_build_main.spl}` —
the native-build driver is **interpreted Simple**, not Rust. ~1 min of
`load_and_merge_module` (852 modules: compiler driver, type_infer, both
backends, linker/ELF writer), log grows 53 KB → 1.1 MB, then total silence.
Last activity: `native_build_parse_closure_owner` span loading
`compiler/backend/linker/_ElfWriter/writer`, then the check-dbs workaround
note. After that, zero trace output for ≥10 min. `/proc/<pid>/io` `rchar`
flat (252484115 → 252484115 / 30 s) during the spin: pure in-memory compute.
5 threads, 1 running; workers idle; CPU pegged (not blocked).

## Root-cause classification

- **Not (a) LLVM-codegen-slow**: no codegen ever starts — the phase is
  pre-backend; zero objects because nothing reaches the object cache.
- **Not (b) an llvm-lane-specific cache/exe-identity defect** (hir_cache
  class): backend-independent AND entry-independent, and it fails before any
  cache-key/identity computation.
- **Not (c) starvation/deadlock**: one hot thread at 95–99% user CPU.
- **(other)** Backend-independent pathological startup cost in the
  seed-interpreted driver, suspected the full-checkout compile-source-inventory
  build / parse-closure publication walk. Prior art in-tree:
  `src/lib/scv/compile_source_inventory_core.spl` comments record "cold
  inventory that was ~200 s of the ~360 s Stage 2 cold init (x86_64)"; the
  interpreted aarch64 seed plausibly costs 50–100× that on a 145k-file
  worktree (possibly quadratic in checkout size). Finite-vs-infinite is
  **unproven**: no phase transition observed in ≥45 min (original lane) or
  10 min (repro); RSS GC cycling hints at progress but there is no progress
  marker to confirm.

## The 2.7 s Cranelift contrast is an artifact

Under byte-identical flags both backends behave identically. No
`examples/hello_world.spl` exists in-tree; the original cranelift lane's
worktree and evidence were removed before this diagnosis; the default cache
(`.simple/native_cache`) is empty and the seed only writes cache at
completion — so the 2.7 s run most likely consumed a pre-populated private
cache from an earlier completed run in that lane (cache-hit path skips the
spinning phase) or measured a different invocation.

## Suggested follow-up

1. Re-run cold under gdb/perf on a ptrace-permitted host to name the exact
   hot function.
2. Check whether the inventory/closure walk is quadratic in checkout file
   count; if so, bound or index it.
3. Add a periodic heartbeat/log line to the interpreted driver's post-load
   startup phases so any future freeze is attributable within one minute.

## Evidence retained (lane-local, untracked)

`build/agent-worktrees/boot-llvmdiagnose/diag/` — per-lane build logs
(`llvm-build.log`, `cranelift-build.log`, `cranelift2-build.log` with span
traces, `plain-build.log`, `tiny-build.log`, `debug-build.log`),
`samples/llvm-5min.txt`, `samples/llvm-9min.txt`.
