# Native text search raw index boundary

Status: source repair prepared; corrected-producer ARM execution and genuine
LLVM 18 RISC-V object qualification pending. Bug database reconciliation is
pending a qualified database tool. This report does not claim bootstrap cache
reuse is repaired.

## Evidence and separate producer lineages

The cache diagnostic used compiler SHA256
`44a540d538241e202e2dc00440591c4fd9567474706c310f3c75367638325134`, constructed
from `cceddeb91c43645e5f70f5cc76ad61daa02562b3` by the Rust bootstrap producer.
Its compiled `hir_cache_load` passed `287 << 3 = 2296` as the third argument to
`rt_text_find`. The function returned raw index `2393`. The following tagged
substring path consumed that raw index as an encoded word and selected the
wrong warning marker. Header newline was 286; the correct warning newline was
288. This is a runtime boundary defect, not evidence of a codec scope failure.

The original evidence is `offline-cursor.log`, `offline-cursor.gdb` and
`offline-loader.log` below:

`/home/yoon/dev/simple-final-frontend-cache-replay-20261011/build/native_probe/hir-v8-qualification/phase3/44a540d538241e202e2dc00440591c4fd9567474706c310f3c75367638325134/cceddeb91c43645e5f70f5cc76ad61daa02562b3/integer-three/cold/`.

Read-only audit identifies the seed counterpart at
`src/compiler_rust/compiler/src/mir/lower/lowering_expr_method.rs`:
the two-argument branch emits `rt_text_find` directly with `arg_regs[1]`.
That bootstrap-generated body uses `rt_slice`. It must be qualified separately;
changing the Pure-Simple MIR source does not modify an existing producer's body.
No Rust source, cache parser, runtime implementation, or constructed compiler
was changed in this repair.

## Pure-Simple owner and contract

The analogous owner is
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`.
`rt_text_find` takes tagged text/text and **raw i64 start**, returning **raw
i64 index**. `rt_string_find` and `rt_string_rfind` also return raw indices.
These signatures and the negative/clamped/empty-needle behavior are confirmed
in `src/runtime/runtime_native.c` and the existing Rust runtime definitions.
Pure-Simple substring/range lowering calls `spl_str_slice` with raw bounds.

`HirTypeKind.Any` parameters are marked by `_MirLowering/function_lowering.spl`;
ordinary MIR i64 parameters are raw. MIR i64 alone cannot distinguish them.
`lower_text_index_operand` uses the existing `is_runtime_value_local` producer
metadata, decoding only tagged values through `decode_runtime_value(i64)`.
That decoder uses `rt_value_as_int_wide`, preserving wide boxed integers.
Raw literals/computed integers pass through without inspecting low bits.
Substring and text range bounds share this helper. Search return locals retain
integer HIR metadata and remain unboxed; 3 is an ordinary result, not nil.
The existing array/slice and custom-method dispatch exclusions are unchanged.

## Regression and qualification

`test/fixtures/text_search_index_abi_native/main.spl` checks computed starts,
typed and erased integer parameters, index 3, negative/past-end starts, missing
and empty needles, aliases, one-argument forward/reverse search, custom method
dispatch, erased substring/range bounds, and the 286/287/288 warning cursor.
Each failure returns a distinct nonzero exit code. Success prints exactly
`text-search-index-abi: pass` and returns zero.

`test/01_unit/compiler/mir/text_search_index_abi_source_spec.spl` guards the
shared provenance-aware owner. Source checks are not native execution evidence.

The one immutable-producer baseline uses CPU 2, one thread, a 120-second
timeout, no stub fallback, and private HIR/frontend/native/root caches at
`build/native_probe/text-search-index-abi/baseline/<producer-sha>/entry/`.
`receipt.json` records argv, environment, fixture identity, exit and time/RSS.
The first invocation stopped before compilation at `SCV-E-ADMISSION:
compile-event-journal-missing`; `admission.log` preserves that failure and the
next invocation initializes the new worktree with
`SIMPLE_SCV_INVENTORY_COLD_INIT=1`.

Baseline result: compilation succeeded in **86.61 seconds**, peak RSS
**1,549,876 KiB**. The native ARM executable returned **5**, the first
`erased_search(source, next)` assertion. Cases 1–4 passed, establishing that
the raw computed start, raw search result 3, substring use of that result,
and typed function start work before the erased integer parameter fails.
There was no stdout or stderr. This separately reproduces the Pure-Simple
owner defect without relying on the seed-generated cache loader.
ARM disassembly confirms the boundary: `erased_search` stores incoming x1
at `0x121bc`, reloads that unchanged word into x2 at `0x1227c`, and calls
`rt_text_find` at `0x12288`. There is no integer decode between them.

Root owns corrected compiler construction. After exact source review and a
new producer receipt, execute the fixture once on ARM, then compile it with
the genuine LLVM 18 provider for `riscv64-unknown-linux-gnu` and require an ELF
relocatable object with machine 243. A RISC-V object is not runtime evidence.
Stop at the first failure, preserve caches, and respect the three-cycle cap.
