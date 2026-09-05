# Minimal Native-Compile Performance Architecture

## Boundary

`app.compiler_perf.minimal_native_compile_perf` owns one benchmark capsule. It
accepts explicit paths and baseline values; it does not discover a compiler or
fall back to another runtime. Standard pure-Simple IO/process facades own file,
clock, and bounded-process effects.

## Flow

1. Verify compiler, receipt, fixture, GNU time, and work directory.
2. Probe `--version`, hash the compiler, and admit the exact receipt tuple.
3. Run five cache-disabled minimal `native-build` processes through GNU time.
4. Admit each artifact by compile status, size, hash, and execution status.
5. Sort five wall-time samples; compare p50, p95, and max RSS to the baseline.

Pure admission, artifact, and budget decisions are separately testable. The
effectful campaign composes them and preserves their first failure reason.
This keeps process authority at the app leaf and leaves compiler layers
unchanged.

## Safety and exclusions

The caller supplies a lane-specific work directory. Only known per-run output
and RSS files inside it are replaced. No shell is invoked. The Rust seed,
unreceipted binaries, Phase 4, and unrelated compiler optimizations are outside
the capsule.
