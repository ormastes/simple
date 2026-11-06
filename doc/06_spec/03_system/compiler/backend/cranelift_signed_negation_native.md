# Native evidence: uniform-I64 signed negation

Requirement: REQ-CRANELIFT-SIGNED-NEGATION.
Executable fixture: `test/fixtures/compiler/cranelift_signed_negation/producer.spl`.
Original failing source: adjacent `source_repro.spl`.

This is a native compiler-boundary fixture, not an executed SSpec-runner report.
It generates an aarch64 object containing fourteen numeric comparisons. The
object's `main` returns the number of mismatches. Compilation alone is not PASS:
run both the generator and the linked generated executable.

1. Create `build/cranelift-signed-negation`.
2. Use an immutable Stage2 compiler with its matching runtime capsule
   to `native-build --backend cranelift --runtime-bundle host-gpu
   --runtime-path <capsule> --source src/compiler --source src/lib --entry-closure
   --entry test/fixtures/compiler/cranelift_signed_negation/producer.spl
   --threads 1 --cache-dir <private>/native
   --output build/cranelift-signed-negation/producer`.
3. Set `SIMPLE_FRONTEND_CACHE_DIR`, `SIMPLE_HIR_CACHE_DIR` and
   `SIMPLE_NATIVE_BUILD_CACHE_DIR` to separate private directories for that run.
4. Run the producer from the repository root. Require exit zero and object
   `build/cranelift-signed-negation/negation.o`.
5. Link with `clang build/cranelift-signed-negation/negation.o -o
   build/cranelift-signed-negation/native-check` and execute that checker.
   Require exit zero: all fourteen generated comparisons matched.

Observed 2026-11-06: build 0, producer 0, link 0, native checker 0.
Cases: i8/i16/i32 minima, positive seven, negative seven and zero (twelve),
i64 negation of -2147483648 and i64 minimum (two).

The helper executed here is the production owner called by
`cranelift_codegen_adapter.spl`. Recompiling the original source fixture with a
new full compiler and running the required core/MCP checks remain admission
requirements; this focused probe does not claim they passed.
