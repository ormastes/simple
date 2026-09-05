# SimpleOS GPU and Knowledge Decision Coverage

Date: 2026-08-02

- Inventory: 71 production decisions / 142 branch outcomes.
- Covered: 140 outcomes.
- Measured coverage: 98% (integer floor).
- Gate: `test/02_integration/app/llm_process/simpleos_gpu_knowledge_decision_coverage_spec.spl`.
- Result: 2/2 scenarios passed.

The inventory requires each decision ID to occur exactly once in production
source and counts explicit true/false witnesses in executable unit tests. The
two uncovered outcomes are valid CUDA and Vulkan ivshmem submissions, which
would touch live MMIO. They remain assigned to the prepared QEMU environment
row; the gate verifies that no unit test invents those witnesses.

This metric covers new owned routing/admission decisions. It does not claim
whole-repository coverage or replace future runtime-instrumented coverage.
