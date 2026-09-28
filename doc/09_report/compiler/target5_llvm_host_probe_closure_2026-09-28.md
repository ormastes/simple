# Target 5 LLVM host probe closure (2026-09-28)

**Focused result: one fewer forbidden kernel import and a smaller host-probe
binary.** `compiler_shared.interpreter.llvm.target` used `app.io.mod` only to
run `uname -m` and `uname -s`. It now calls the existing
`std.io_runtime.process_run` facade with the same arguments and retains the
same output mapping and fallback values. The Linux integration spec reports
**1 example, 0 failures** both before and after.

The widened closure audit changed from `3 K0->P, 14 K1->P, 10
kernel->app/os, 0 unresolved` to `3 K0->P, 14 K1->P, 9 kernel->app/os,
0 unresolved`, with 2,085 classified files in each run. The audit still
fails overall.

| Focused no-stub entry-closure measure | Before | After |
|---|---:|---:|
| Compiled source units | 90 | 41 |
| Native binary size | 126,872 B | 115,336 B |
| Paired process wall p50, 30 samples | 10.214 ms | 7.918 ms |
| Paired process wall p95, 30 samples | 11.227 ms | 8.795 ms |
| Maximum process RSS, 30 samples | 1,488 KiB | 1,488 KiB |

The size difference is **-11,536 B (-9.09%)** for this focused spec binary.
The time ratio is **0.783368** and the RSS ratio **1.000000**, for a normalized
sum of **1.783368**. Each pair alternated order on the same Linux host. Wall
time includes process launch and the two host probes; it is not a full
compiler startup or release-small hello measurement. Sample rows are in
`target5_llvm_host_probe_samples_2026-09-28.tsv`, SHA-256
`b208672b1b6b51d0ccffbc06e017eacd37763a8b0c1690db47c9ad958cc3b53e`.

The before/after binary SHA-256 values are
`565a0d5cd8aa678ef2bfae3a41a7072bbe47a30ef7a12eee4e33259bec0f3d40`
and `adbd95d6b8020bbf2f85a5f27623832af944adeeb1ef35568b629558fca8d9ab`.
Both were built with the admitted pure-Simple Stage2 compiler SHA-256
`d57b8ff1c676c0e250f76f713a5e8e5b0bbf3d91fd72741698e8fe0f26ad033c`.

The 15 KiB matched hello size gate, Python-relative startup/RSS gate, and
full kernel demand-load qualification remain open.
The required core runtime smoke could not pass on the available Stage2
binary: it rejects `-c` as an unknown command. The MCP native smoke stops
before execution because `bin/simple_mcp_server` is absent in this worktree.
These focused native results are not a substitute for those broad checks.
