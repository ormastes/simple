<!-- codex-research -->
# Full Pure-Simple SIMD Bootstrap: Domain Research

Date: 2026-09-07

## Capability detection and execution safety

AVX-512 is a family of independently advertised features, not one boolean. Safe user-space execution requires CPUID OSXSAVE support, XGETBV confirmation that XMM/YMM and opmask/ZMM state are enabled, AVX512F, and every additional subset used by a kernel such as BW, DQ, VL, or CD. The design should expose feature bits and kernel requirements, then dispatch only when their conjunction holds. Sources: [Intel 64 and IA-32 Software Developer Manuals](https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html) and [Volume 1 PDF](https://cdrdv2-public.intel.com/671436/253665-sdm-vol-1.pdf).

Arm ACLE distinguishes Advanced SIMD (NEON), SVE, and SVE2. Linux exposes user-space capabilities through `AT_HWCAP`; compile-target macros alone do not establish runtime availability. SVE kernels must be vector-length agnostic and strip-mine using the runtime vector length. Sources: [Arm C Language Extensions](https://arm-software.github.io/acle/main/acle.html) and [Linux arm64 ELF hwcaps](https://www.kernel.org/doc/html/latest/arch/arm64/elf_hwcaps.html).

RISC-V V defines implementation-dependent VLEN/ELEN and runtime `vl`, `vtype`, and `vlenb`. Portable kernels use `vsetvl` strip mining and explicitly define mask/tail policy; they must not assume 128-bit vectors. Source: [RISC-V Vector Extension specification](https://docs.riscv.org/reference/isa/unpriv/v-st-ext).

WebAssembly SIMD uses fixed-width `v128` values with specified lane interpretations. SIMD instructions affect module validation, so deployment needs a supported SIMD module plus a scalar variant or selection before loading an unsupported module. Source: [WebAssembly SIMD proposal](https://github.com/WebAssembly/spec/blob/main/proposals/simd/SIMD.md).

## Semantic portability

Integer byte/word operations can usually require exact scalar equivalence. Floating-point reductions need an explicit policy because vector reassociation, fused operations, signed zero, NaN payloads, and rounding can differ from sequential scalar evaluation. A portable API should distinguish exact operations from reductions allowed to use a documented numerical contract.

Fixed-width ISAs can use constant-size chunks with a bounded scalar tail. SVE and RISC-V V should use predication/strip mining. One public API can support both when the backend owns width and mask formation and callers express operations in semantic terms rather than register widths.

## Database and web-server applications

SIMD is well suited to classification, delimiter search, equality/prefix checks, bitmap operations, UTF-8 validation, hashing primitives, and selected numeric scans. It is less predictably useful when allocation, pointer chasing, branching, syscalls, or number conversion dominate, so each integration needs representative measurement.

The simdjson design demonstrates that wide structural classification and UTF-8 validation can accelerate parsing while maintaining a scalar-equivalent semantic oracle. Its results support applying SIMD to HTTP/JSON classification stages, but do not prove gains for this repository's complete request pipeline. Source: [Parsing Gigabytes of JSON per Second](https://arxiv.org/abs/1902.08318).

Database scans should preserve row ordering and null/type semantics. Bitmap fusion, byte comparisons, delimiter search, and fixed-width numeric predicates are safer first targets than changing query planning or storage layout. Web integration should preserve RFC-visible parsing and serialization results, enforce request-size bounds before vector reads, and retain exact tail handling.

## Architecture implications

1. Capability discovery should return granular features and OS-state readiness; each kernel declares its minimum feature set.
2. The public API should be target-neutral and pure Simple. Target lowering belongs in compiler/HAL layers below it.
3. A scalar implementation is the semantic oracle and mandatory fallback, not a placeholder.
4. Fixed and scalable vectors should share operation semantics while allowing different loop construction.
5. Dispatch should be cached outside hot loops and remain observable in retained benchmark/evidence receipts.
6. Deployment proof must bind performance and correctness evidence to the exact admitted Stage 4 binary, because source-level capability alone does not prove the executable users run contains it.

