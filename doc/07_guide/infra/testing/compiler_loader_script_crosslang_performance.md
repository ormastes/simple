# Compiler, loader, and script cross-language performance evidence

Use this protocol for Simple comparisons with Python, Rust, C, Go, or Bun and for module-resolution cache changes.

## Admit before measuring

1. Record host/tool versions and executable path/hash.
2. Prove Simple is current and self-hosted; reject seed, hybrid, stale, unknown, unexecuted, or hash-mismatched artifacts.
3. Prove requested mode equals actual mode and fallback is false.
4. Verify exit status, observable checksum, and workload semantics.
5. Only then report timing, RSS, syscalls, or ratios.

Do not infer mode from command spelling or time discarded results. Rust is required when installed; absent toolchains are explicitly unavailable.

Keep cold-start, warm-runtime, compiler-check, loader, and script workloads separate. Retain warmups, iterations, samples, p50/p95, maximum RSS, CPU policy, raw argv with boundaries, checksum, and rejection reason. Each retained row keeps distinct compiler/runtime/script/loader paths and SHA-256 values where applicable; do not collapse them into one executable field. Build time belongs only to named build rows.

The cross-language harness requires `timeout` and `/usr/bin/time` before it creates artifacts. Its numeric environment knobs must be positive or non-negative integers as documented by their workload semantics; malformed or zero values are untestable. The default raw-artifact directory is `build/test-artifacts/05_perf/compiler_loader_script_crosslang_perf/`.

Byte evidence validates requested length, boundary bytes, and checksum before memory. Report total RSS and a same-executable/mode zero-payload delta; the selected gate remains peak RSS ≤4× payload, otherwise a blocker. Loader evidence compares failed metadata probes using the same classifier/fixture and requires ≥90% reduction without semantic, p95, or RSS regression.

An unresolved import may be reused only while resolution context is unchanged. Cache presence is explicit; empty text cannot mean both no entry and cached miss. Reset/context mutation invalidates positives and negatives. Test that a newly created module is visible after reset.

Rejected diagnostics may locate bugs but cannot support release/cross-language claims. Preserve raw evidence under `build/test-artifacts/` and summarize admitted rows in the generated manual.
