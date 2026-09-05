# Cosmos NVMe Media Policy Evidence Plan

## Requirement trace

- REQ-004: retain exact NVMe validation, completion, dispatch, and media-span
  behavior across the Pure Simple boundary.
- REQ-011: provide executable hardware-independent boundary and error evidence.
- NFR-006: prove allocation-free host/ARM objects and closed ARM policy links.
- NFR-010/NFR-012: fail closed on absent evidence and keep the claim explicitly
  below board acceptance.

## Gates

1. Pin the 36-function version-1 header ABI and the exact per-consumer import
   and public-export sets without changing the consumers.
2. Compile the independently named frozen C oracle with strict diagnostics;
   reject any production-policy definition or import.
3. Run exactly 196 frozen rows, bind function identity, arity, runtime inputs,
   results, and row into digest `b6a2f693699eb752`, and require 259/259 LLVM
   C-oracle branches.
4. With admitted Stage 4 only, link the generated host owner into the same
   vector runner and require exact row parity.
5. Compile the production Simple coverage probe with compiler instrumentation,
   bind 63 runtime rows to the source-hashed decision manifest, and require
   126/126 edges. Owner-authored counters are forbidden.
6. Run the focused Pure Simple unit spec and accept only its exact canonical
   `executed=4 passed=4 failed=0 dropped=0` verdict; generate an ELF32 ARM
   owner and resolve all policy imports from the unchanged firmware, dispatch,
   and FTL-media ARM objects.
7. Hash the frozen inputs and retained evidence into the lane receipt. Leave
   board, QEMU, endurance, and whole-NVMe status separate.

## Stop conditions

The source/C lane provides diagnostics only when the frozen rows, C coverage
denominator, exact signatures, and static ABI closures match; it retains no
PASS receipt by itself. The runtime lane returns `BLOCKED`, not PASS, when
admitted Stage 4 is absent. Any parity, edge, ABI, allocation, provenance, or
input-revalidation mismatch is a hard failure.
