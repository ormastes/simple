# Target 5 current-source Stage4 compiler diagnostic (Linux ARM64)

Status: diagnostic native link and smoke PASS; production qualification OPEN.

The current pure-Simple bootstrap coordinator built the same 860-unit compiler
entry closure twice on Linux aarch64 with Cranelift, no stub fallback, and
current source. The dynamic build used `--runtime-bundle dynamic-runtime`,
`SIMPLE_COMPILER_ENTRY_STAGE4=1`, and the current shared runtime plus compiler
backfill. The static comparator used `--runtime-bundle simple-core` with the
current `libsimple_native_all.a`. That archive is a hosted bootstrap aid, so
this pair is a controlled diagnostic, not an admitted production baseline.

| Measurement | Dynamic | Static diagnostic |
|---|---:|---:|
| Unstripped executable bytes | 23,067,424 | 29,809,584 |
| Unstripped shared runtime bytes | 10,072,672 | 0 |
| Unstripped deployment bytes | 33,140,096 | 29,809,584 |
| Stripped executable bytes | 16,213,880 | 19,671,600 |
| Stripped shared runtime bytes | 3,174,656 | 0 |
| Stripped deployment bytes | **19,388,536** | **19,671,600** |
| 30 paired `--version` p95 wall startup | 2.860 ms | 3.262 ms |
| 30 paired maximum process RSS | 6,808 KiB | 7,820 KiB |

The dynamic stripped executable is 17.6% smaller. Including its one shared
runtime gives a 283,064-byte (1.44%) smaller single-tool deployment than the
static comparator. Before stripping, the dynamic deployment is 3,330,512
bytes (11.17%) larger, mainly because the shared runtime retains debug and
symbol data. The measured p95 startup and maximum RSS are lower in this
diagnostic cohort. Samples alternate execution order in 30 pairs and use
`/usr/bin/time` for child RSS and monotonic host wall time for startup. The
raw samples are in
`target5_stage4_dynamic_vs_static_startup_samples_2026-09-29.tsv` (SHA-256
`f6dc379458f16f0d2b2632fe4b139541241f3785e251a7f99eb472f0b28c342f`).
Small millisecond timings remain sensitive to host scheduling.

The dynamic compiler's unstripped SHA-256 is
`a5d49919b4aca32b94fc5ff6d71d4119da3baf9602c65ab9f0ed22a0ec27c5f5`.
It links `libsimple_runtime.so.0`, exits zero for `--version`, and checks
`test/05_perf/fixtures/interpreter_startup/hello.spl` with zero errors (0.15 s,
12,160 KiB peak RSS). The static comparator's unstripped SHA-256 is
`18d7ff32a68e78a2e7874fea78be25e9a95e1c0f9c60c165b7bea544e5ad9fc8`.

The compiler-entry build does not exercise the full CLI's optional provider
closure. The static archive is not a release baseline. This report does not
close the Linux matched-startup hello size gate, the 100-sample release cohort,
zero optional-provider startup trace, kernel closure, or Phase 7 provenance and
residency receipt requirements. Those remain tracked in
`doc/08_tracking/todo/target5_target6_completion_2026-09-27.md`.
