<!-- codex-research -->
# CUDA/Vulkan Interop — NFR Options

User selection is required before implementation.

## N1 — Production fail-closed evidence (recommended)

**Targets:** 80%+ branch coverage; exact UUID match; zero placeholder passes;
device-origin checksum; timeline ordering; bounds/lifetime/device-loss tests;
no capability promotion on skip; no CPU staging in admitted steady state;
current-host environment receipt plus negative emulated/SimpleOS receipts.

**Pros:** Strong truthfulness and release safety. **Cons:** More harness/runtime
work. **Effort:** L, 8-14 test/evidence files in addition to F1.

## N2 — Contract-only portability matrix

**Targets:** 80%+ branch coverage for pure negotiation and receipt classifiers;
documented Linux/Windows/SimpleOS/Adreno/Metal matrix; native interop remains a
manual experiment.

**Pros:** Fast and portable. **Cons:** Does not prove external libraries or GPU
behavior. **Effort:** M, 5-8 files.

## N3 — Research-grade spatial proof

**Targets:** N1 plus pinned driver/toolkit/kernel-module hashes, profiler counter
evidence of overlap, isolation/fault-injection tests, 4-to-8192 buffer benchmark,
and independent reproduction instructions.

**Pros:** Only option that could truthfully promote VUDA/spatial concurrency.
**Cons:** Impossible until code is published; high security and maintenance
cost. **Effort:** XL+, environment-dependent.
