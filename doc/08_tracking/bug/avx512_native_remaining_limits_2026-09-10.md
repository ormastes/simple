# AVX-512 native remaining limits (2026-09-10)

Status: **fixed 2026-11-06** on `work/avx512-backend-harden-20261106` (base
`origin/release/1.0.0` 376bf9deb3c) except the items under "Still open" below.
Original status: known issues on `review/avx512-simd-wip-20260909`.

## Non-AVX-512 routing safety

`x86_avx512_handles` currently claims every SIMD MIR operation, including
operations whose locals have no 512-bit shape. `isel_block_with_x86_simd` can
therefore route ordinary AVX2/SSE operations through the AVX-512 frame owner
when `avx512_shapes` is empty. A non-AVX-512 host may then panic on a missing
frame shape or emit a 64-byte operation. The owner must reject empty shape sets
and only claim operations whose participating locals belong to the AVX-512
frame. Add forced-disabled and mixed-width regressions.

## Native ABI and allocation limits

- AVX-512 vector arguments and return values are rejected by
  `x86_64_avx512_isel.spl`; the native vector ABI is not implemented.
- General-purpose-register spills in the AVX-512 allocator still panic.
- Explicit 512-bit MIR rejects compilation when AVX-512 is unavailable. The
  native path does not automatically scalarize or select the portable
  interpreter fallback.

## Verification limits

- The existing owner-routing test covers scalar constants and `Vec16i`, but
  does not cover `Vec8f`, `Vec8i`, an empty shape map, or mixed AVX2/AVX-512
  functions.
- The draft branch contains the pure-Simple selector, lowerer, encoder, and
  interpreter, but also includes runtime C capability probes and Rust bootstrap
  glue. It is therefore not yet a wholly pure-Simple implementation boundary.
- The branch must be rechecked against current `main`; its open PR was based on
  an older commit and reported conflicts and a failing publish check.


## Resolution 2026-11-06 (work/avx512-backend-harden-20261106)

| Item | Root cause | Fix | Commit |
|---|---|---|---|
| Routing safety | (already fixed) `x86_avx512_handles` claimed SIMD with no planned shape | empty-shape guard `x86_64_avx512_lower.spl:26` (now further down after the ABI header); pinned again in `x86_avx512_isel_fallback_spec` | — |
| Cross-width copy | `x86_64_avx512_isel.spl:84-85` recorded narrow vectors with an `A \| B` pattern that never matched a Vec8f local, so Vec16f -> Vec8f planned ok | refuse any data copy whose destination is not declared as a 512-bit frame vector | a19e5f37ced |
| GPR spill panic | `regalloc.spl:393` panicked; the generic rewriter put spill slots at rbp-8 on top of the isel frame, used allocatable R10/R11 as scratch, reused R10 for a third operand and substituted RAX for a spilled memory base | AVX-512 frame functions: rerun linear scan without R10/R11 when spilling, slots below `func.frame_size`, one scratch per spilled vreg, push/pop borrow for a third | 116f883951d |
| No scalar fallback | `isel_x86_64.spl:192` panicked when the capability was denied | the same frame plan lowered lane by lane (`x86_64_avx512_scalar.spl`): GPR + SSE scalar only, no EVEX/ZMM/k; FMA refused by name (`E-BACKEND-X86-AVX512-SCALAR-FMA`) because SSE2 cannot round once | 911dbe5f968 |
| Vector argument/return ABI | `x86_64_avx512_isel.spl:82,88` rejected `Arg` vectors and vector returns | frame-vector ABI v1: vector args by address (one integer slot, copied in the prologue), hidden result pointer in slot 0 returned in RAX; identical with and without AVX-512; stack-slot vector args, vector call terminators and indirect calls fail closed with named reasons | 911dbe5f968 |
| AVX2/AVX-512 mixing | AVX2 planner seeded its kind from i32x8 index loads of f64x8 permute/gather/scatter and demanded an AVX2 capability | i32x8 index vectors stay in the AVX-512 frame plan | 911dbe5f968 |

Encoder defects found by executing the backend output (Xeon W-2135, AVX-512F/BW/VL),
all invisible to the previous byte tests — commit 6df2ddfeade:

- `encode_x86_64.spl` `encode_mem_operand`: RBP/R13 base with a non-zero displacement
  emitted no ModRM/displacement at all (SIGSEGV on the first AVX-512 function: the
  callee-save stores decoded as other instructions). Affects every x86 `[rbp-n]` MOV.
- VPBLENDMD/Q emitted in map 0F3A instead of 0F38: #UD on every select.
- VPMOVSXDQ emitted with F3 (= VPMOVSQD): every f64x8 permute/Reverse/Interleave wrong.

Receipt truth (commit 2a50e60def8): `@must/@prefer(avx512)` is now also judged on the
emitted bytes (`x86_64_avx512_receipt.spl`, SIMD-REQ-002): satisfied only if the
decoded machine code contains an EVEX L'L=10 instruction.

Evidence:
- `test/02_integration/compiler/native/x86_avx512_exec/run_x86_avx512_exec.shs`:
  `SUMMARY executed=222 compared=109 mismatched=0 refchecked=222 refbad=0`
  (every f32x16/f64x8/i32x16 family, the call ABI and a 20-live-GPR spill case, both
  modes, vs an independent C reference).
- New specs (seed `simple.exe test`, all passing): `x86_avx512_evex_llvm_golden_spec` 10/10,
  `x86_avx512_scalar_fallback_encoding_spec` 11/11, `x86_avx512_isel_fallback_spec` 7/7,
  `x86_avx512_receipt_truth_spec` 10/10, `x86_avx512_regalloc_spill_guard_spec` 5/5,
  `x86_avx512_exec_dump_spec` 1/1. Byte goldens come from llvm-mc 23.1.0
  (`x86_avx512_evex_goldens.shs`, `x86_avx512_scalar_fallback_goldens.shs`).

## Still open

- Exact FMA without AVX-512: refused by name, not emulated.
- The generic (non-AVX-512) x86 spill rewriter in `regalloc.spl` `rewrite_inst` keeps
  the defects listed above (slots at rbp-8 overlapping the isel frame, R10/R11
  allocatable yet used as scratch, R10 reused for a third operand, RAX substituted for
  a spilled memory base). Only AVX-512 frame functions use the new path.
- The x86 callee prologue loads only register-slot arguments; stack arguments are never
  loaded (generic). The frame-vector ABI refuses vector arguments that would land there.
- `x86_avx512_mir_pipeline_spec` "keeps AVX2 values live across AVX-512 scratch
  operations" still fails with `simd-register-pressure`: in mixed functions the AVX2
  planner has only YMM4..5 and does not let a dying load-defined source back the
  binop result. Pre-existing; AVX2 planner owner.
- The remaining verification item about runtime C capability probes and Rust bootstrap
  glue is unchanged (not part of this backend change).
