# Target 5 current-source Linux ARM64 hello diagnostic

Status: current-source absolute size and diagnostic startup/RSS measured;
production qualification OPEN.

A current-source pure-Simple bootstrap coordinator (SHA-256
`21aecdb2a41867b0ce2098fe05844722ab9742b483ec1e72aecb84f3b2f5d175`)
built `test/05_perf/fixtures/interpreter_startup/hello.spl` with Cranelift,
`--entry-closure`, `--runtime-bundle core-c-bootstrap`, no stub fallback,
`--strip`, and `aarch64-unknown-linux-gnu`. The binary prints exactly
`Hello World\n` and has only libc in `DT_NEEDED`.

| Linker selection | Stripped ELF bytes | Relative to 15,360-byte cap |
|---|---:|---:|
| Default C driver linker | 21,016 | 5,656 over |
| Explicit `SIMPLE_LINKER=lld` | **14,560** | **800 under** |

The explicit LLD build is 6,456 bytes (30.72%) smaller. In its ELF, `.dynsym`
is 720 bytes versus 4,968 bytes with the default linker. This is strong
attribution for the file-size change, but it does not identify every retained
section or prove the remaining 1.05x matched-startup C ratio. The LLD binary
SHA-256 is
`3a22e7103358b3a2c1a3fd6eb554dbd685a0c80073721129f7260901f480bece`.

Thirty alternating same-host pairs ran that LLD hello and
`test/05_perf/fixtures/interpreter_startup/hello.py`, checking exact output
and zero exit each time. Child RSS came from `/usr/bin/time`; startup is
monotonic host wall time including process launch.

| Measurement | Simple hello | Python hello |
|---|---:|---:|
| p50 startup | 1.445 ms | 16.432 ms |
| p95 startup | 1.831 ms | 19.226 ms |
| Maximum process RSS | 1,076 KiB | 9,380 KiB |

Raw rows are in `target5_current_hello_lld_python_startup_samples_2026-09-29.tsv`
(SHA-256 `2dbc9e7aa9f426be5c3047ff90e4b4825c243bbddcc750255e821ef13ba66825`).
The cohort is directional: it lacks an admitted Stage4 producer receipt,
matched C binary built with the same current startup objects and runtime
archive, provider/no-GC traces, and the 100-sample release cohort. The
historical C-authored pair in `target5_strict_core_hello_2026-09-27.md` is a
different source snapshot and cannot serve as this binary's denominator.

The current link still force-roots `__simple_runtime_init`,
`__simple_runtime_shutdown`, `prof_sample_force_link`,
`rt_function_not_found`, `rt_set_args`, and `rt_string_bytes`. The stripped
artifact cannot prove whether the plain-literal lowering removed every
requested internal symbol; a retained link map or unstripped object inventory
is still needed. No full CLI optional-provider or Phase 7 gate is closed.
