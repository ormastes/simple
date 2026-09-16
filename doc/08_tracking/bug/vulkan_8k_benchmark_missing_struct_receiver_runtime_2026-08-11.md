# Vulkan 8K benchmark blocked by missing struct-receiver runtime symbol

Date: 2026-08-11

## Reproduction

```sh
VK_ICD_FILENAMES=/usr/share/vulkan/icd.d/lvp_icd.json \
SIMPLE_TIMEOUT_SECONDS=300 \
bin/simple run test/05_perf/graphics_2d/bench_vulkan_8k_retained_damage.spl
```

## Actual result

Cranelift code generation panics while compiling `main` because
`rt_struct_receiver_valid` is absent from the deployed runtime function table.
The driver then falls back to the interpreter. The process grows to
approximately 12,967,500 KiB maximum RSS and is terminated before the
benchmark emits a frame receipt.

Stub fallback is not an acceptable workaround: it would silently invalidate
Vulkan backend behavior. The Rust bootstrap seed is likewise not an admitted
replacement for the pure-Simple self-hosted toolchain.

## Expected result

The deployed self-hosted runtime provides every receiver-guard symbol emitted
by its code generator, or rejects the build before execution with a bounded
diagnostic. The benchmark then executes natively without interpreter fallback.

## Impact

Blocks end-to-end 8K Vulkan LOCAL-frame measurement including dispatch,
submission, completion, partial readback, checksum, RSS, and fallback receipts.
Transfer-only Rust-runtime evidence remains valid but cannot substitute for
this renderer-level gate.

The same stale-runtime defect also blocks the software retained-frame timing
gate `test/perf/graphics_2d/bench_damage_checksum_8k.spl`. On 2026-08-11 it
forced interpreter fallback; the 8K seed/run exceeded the default 60-second
CPU guard and one bounded 240-second retry without emitting a result row. This
does not contradict the focused incremental-checksum correctness PASS, but it
prevents an honest 8K p50/p95 claim for that path as well.

## Acceptance

1. Rebuild/deploy the pure-Simple runtime with `rt_struct_receiver_valid`.
2. The reproduction runs without JIT stub or interpreter fallback.
3. Maximum RSS remains bounded and the benchmark emits exactly one
   `VULKAN_8K_RETAINED` result.
4. Receipt identifies device type/driver and does not promote llvmpipe to
   physical-GPU evidence.
