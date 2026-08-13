# Compiler, loader, script, and cross-language performance B+B

Status: focused source contract; retained runtime timing remains open. Failed
existence-probe evidence is now an executable deterministic gate, not syscall
evidence.

Executable source: `test/05_perf/compiler_loader_script_crosslang_perf_spec.spl`.

The spec proves exact repeated negative-cache reuse, caller-sensitive cache-key
separation, and reset invalidation through `module_resolve_uncached_count()`.
It also audits the retained profile for self-hosted provenance, bounded
execution, Rust/C/Go/Python/Bun parity, explicit native byte-fixture mode, and
exact 1/4/32 MiB byte checks. The Linux-only byte producer requires GNU
`/usr/bin/time` and `timeout`; a focused contract proves fast-exit RSS, known
child inclusion, and bounded timeout failure. Unsupported hosts are unavailable,
and no unbounded fallback is admitted. It rejects total process RSS above four
times payload and enforces the fixture's 1 MiB `<1000 ms` and 32 MiB `<30000 ms`
receipts while retaining separate host wall samples.

The gate opens a facade measurement generation and compares 100 cache-reset
misses with 1000 retained requests. It requires identical resolution, uncached
counts of 100 and 1, a positive baseline of **failed existence probes**, and a
90% reduction (`cached * 100 <= baseline * 10`). The packed result contains
total in high 31 bits and failed in low 32 bits; negative values are errors.
The shared invariant is `failed <= total <= 0x7fffffff`. A deterministic direct
facade check asserts exact `(total, failed) = (2, 2)` using a per-process path
that is required to be absent without deleting it.
Native providers admit a generation lease before the facade filesystem work,
clear accepting before drain, and use a 63-bit no-wrap token that fails closed
at overflow. The source gate does not claim disabled-path assembly or cycles.
It does not claim a timing benchmark, a filesystem syscall reduction, or a
Stage 4 admission.

The focused C selfcheck is separate from the Simple SSpec: it compiles and runs
the test-only counter-seed harness against both C providers. Its PID-scoped
fixture must already be absent and is never deleted.
