<!-- codex-architecture -->
# GPU/Web Differential Oracle — TLDR

- `common.spec.differential_trace` owns immutable `TraceEvent` and
  `NormalizedTrace`; production may emit them through an injected test sink.
- `std.test.differential_conformance` owns comparison, environment policy,
  object-ID mapping, mutation rejection, and test-only oracle descriptors.
- Future `std.gpu.reference_oracle_sffi` dynamically loads Mesa/Vulkan only as
  a verified test oracle; production never imports it.
- Compare ordered semantic transitions, errors, mapped lineage, and digest/
  scalar facts—not raw protocol bytes or cross-provider timestamps. Incomplete
  or dropped traces fail; device pixels remain exact observations.
- VUDA has no current repository use; do not migrate or add it.

See [full architecture](gpu_web_differential_oracle.md) and
[detail design](../05_design/gpu_web_differential_oracle.md).
