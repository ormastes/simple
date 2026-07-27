# ProcessingIR GPU Offload Break-Even Measurement

## Scope

This plan measures whether a real ProcessingIR submission should stay on the
CPU or be offloaded to CUDA/Vulkan. The decision uses device execution plus
host/device communication, including the measured transfer/readback phase.
Device-kernel time alone is not an offload win.

The executable consumer is:

```text
test/03_system/app/simpleos_gpu_host/processing_ir_offload_break_even_spec.spl
```

It accepts no synthetic rows and does not use `pass_todo`. On Linux, missing
or malformed evidence fails. On macOS, this lane is postponed to the macOS
Metal host owner; the macOS host test must produce the same receipt shape
before it can claim a live result.

## Current Commands

Run the producer self-test first. This checks receipt validation without
claiming a GPU result:

```sh
sh scripts/check/check-processing-ir-offload-break-even.shs --self-test
```

Run the live Linux CUDA producer:

```sh
sh scripts/check/check-processing-ir-offload-break-even.shs
```

It writes the structured receipt at:

```text
build/simpleos_gpu_host/offload_break_even/evidence.env
```

For retained or alternate evidence, the consumer accepts an explicit path:

```sh
SIMPLE_GPU_OFFLOAD_BREAK_EVEN_RECEIPT=build/<run>/evidence.env \
  bin/simple test \
  test/03_system/app/simpleos_gpu_host/processing_ir_offload_break_even_spec.spl \
  --mode=interpreter --no-daemon
```

The retained 2026-07-26 C harness measured CPU decisions at 64 and 65,536
elements, generated-CUDA decisions at 1,048,576 and 8,388,608 elements, and a
break-even batch of 1,048,576 with 1,832 us median communication overhead.
That harness validates generated 2D PTX, device execution, transfer, and exact
readback; it is backend calibration, not direct
`processing_ir_execute_cuda` evidence.

The direct ProcessingIR gate uses the same policy threshold:

```sh
PROCESSING_CUDA_FILL_MODE=large \
  sh scripts/check/check-processing-cuda-fill-native.shs
```

Its retained candidate returns all 1,048,576 exact values with positive
provenance and no fallback. Bulk runtime-owned readback conversion reduced its
cold execution from 1,044,501 us to 593,323 us. A retained-session probe then
completed the same exact request in 861,499 us cold and 69,331 us warm (12.4x
faster).

The source-matched daemon-wire gate now passes three warmups plus five measured
1,048,576-element requests. Its measured medians are 155,110 us device,
312,012 us round trip, 156,902 us non-device overhead, and 82,097 us for the
independent CPU oracle. Every receipt has exact output/checksum and stable
positive CUDA provenance. Because device time is slower than the CPU oracle,
the policy correctly reports `available-not-preferred`.

The daemon now runs that independent CPU allocation only when the evidence
harness passes `--processing-verify-cpu`, or lazily when CPU fallback is
actually selected. Default strict GPU requests validate FillU32 output directly
and no longer duplicate the full processing workload on the CPU. Exact FillU32
validation is fused into the runtime-owned wire copy/checksum pass, eliminating
another full production-side array scan while preserving fail-closed mismatch
handling.

Use the retained-session wrapper in two distinct modes:

```sh
SIMPLEOS_GPU_FALLBACK_WIRE_MODE=device-warm \
  SIMPLEOS_GPU_HOST_BIN=build/simpleos_gpu_host/device_warm_wire/simpleos_gpu_host-source-matched \
  SIMPLEOS_GPU_FALLBACK_WIRE_PROBE_BIN=build/simpleos_gpu_host/device_warm_wire/fallback_wire_probe \
  sh scripts/check/check-simpleos-gpu-fallback-wire.shs

SIMPLEOS_GPU_FALLBACK_WIRE_MODE=device-warm-production \
  SIMPLEOS_GPU_HOST_BIN=build/simpleos_gpu_host/device_warm_wire/simpleos_gpu_host-source-matched \
  SIMPLEOS_GPU_FALLBACK_WIRE_PROBE_BIN=build/simpleos_gpu_host/device_warm_wire/fallback_wire_probe \
  sh scripts/check/check-simpleos-gpu-fallback-wire.shs
```

Evidence mode requires an explicit verifier-enabled startup receipt and eight
CPU/device comparison records with positive timings. Production mode requires
an explicit verifier-disabled receipt and no comparison records. Under the
prior checker, the retained pre-optimization daemon passed evidence mode with
medians `116663 us` device, `236498 us` round trip, and `119835 us` non-device
overhead, then production mode rejected its comparison records with
`unexpected-cpu-verification`. It predates the startup receipt, so the
strengthened checker rejects it with `daemon-verifier-mode-mismatch`; those
numbers are historical baseline only.

Fresh optimized medians remain open. The retained pure-Simple compiler rejects
the valid multiline initializer at
`src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl:847`, so it cannot build the
current daemon closure. Resume with an admitted current-source compiler and the
second command; do not treat the retained-daemon rejection as performance
evidence.

The fused runtime helper passes its focused unit 1/1 and the policy contract
passes 10/10. A newer provenance-bound pure-Simple Stage3 with SHA-256
`af6a3e1b19156793bba13f7294ba60319cca1c31abdfffed68a7f49472f862e9`
reproduces the same parser failure, so it is not an admitted daemon producer.
The refreshed runtime capsule SHA-256 is
`0efd7e3f0f8e2aeda7eb5720df5c67717348772b56bc29ba4f6efaa174591658`;
its symbol table includes both checksum helpers, and a two-module pure-Simple
native probe passes exact copy/checksum, mismatch, and extra-length rejection.

## Unavailable Protocol

If the requested native device, driver, or runtime is unavailable, the
producer must write a diagnostic receipt instead of fabricating timings:

```text
processing_ir_offload_status=unavailable
processing_ir_offload_schema=processing-ir-offload-v1
processing_ir_offload_execution=processing_ir
processing_ir_offload_backend=cuda
processing_ir_offload_reason=<non-empty stable token>
```

An unavailable receipt must contain no rows, break-even batch, or measured
RSS/timing values. It is diagnostic evidence only: the Linux consumer remains
non-pass and exits nonzero, while macOS may retain this status during its
postponed-host phase. Neither host may promote it to a GPU result.

## Measurement Rules

- Use a native ProcessingIR path and record the selected backend (`cuda`,
  `vulkan`, or `cuda+vulkan`); do not use a CPU mirror as device evidence.
- Run at least 3 warmup samples and at least 5 measured samples per batch.
- Discard warmups. Report the median of the measured samples for every field.
- Use a monotonic microsecond clock for CPU, device, transfer, and total time.
- Use identical input and output work for the CPU baseline and GPU path.
- Keep batch sizes strictly increasing and choose sizes that bracket a measured
  transition from slower to faster GPU round-trip.
- `total_us` is the median measured end-to-end round trip and is required to
  equal `device_us + transfer_us` exactly for every row. The compatibility
  field `transfer_us` is the non-device remainder, covering launch,
  synchronization, and all host/device communication needed by the result.
- The break-even batch is the smallest row whose measured `total_us` is less
  than `cpu_us`. At least one smaller row must be non-faster and choose CPU.
- A row with `total_us >= cpu_us` must report `decision=cpu`; it is not allowed
  to claim a GPU win based only on device time.

## Receipt Schema

The file is newline-delimited `key=value` text. Required header fields:

```text
processing_ir_offload_status=pass
processing_ir_offload_schema=processing-ir-offload-v1
processing_ir_offload_execution=processing_ir
processing_ir_offload_backend=cuda|vulkan|cuda+vulkan
processing_ir_offload_aggregate=median
processing_ir_offload_timing_unit=us
processing_ir_offload_warmup_samples=<integer >= 3>
processing_ir_offload_measured_samples=<integer >= 5>
processing_ir_offload_row_count=<integer >= 3>
processing_ir_offload_break_even_batch=<integer>
processing_ir_offload_rss_source=procfs
processing_ir_offload_cpu_rss_kb=<positive integer>
processing_ir_offload_gpu_rss_kb=<positive integer>
processing_ir_offload_peak_rss_kb=<positive integer>
processing_ir_offload_communication_overhead_us=<non-negative integer>
```

For each zero-based row index from `0` through `row_count - 1`, emit:

```text
processing_ir_offload_row_N_batch=<positive integer>
processing_ir_offload_row_N_cpu_us=<positive integer>
processing_ir_offload_row_N_device_us=<positive integer>
processing_ir_offload_row_N_transfer_us=<positive integer>
processing_ir_offload_row_N_total_us=<positive integer>
processing_ir_offload_row_N_decision=cpu|gpu
```

The consumer checks strictly increasing batch sizes, exact total accounting,
CPU/GPU decision consistency, a slower row below the threshold, and a faster
row at or above it. It does not impose an absolute speed target because GPU
model, driver, power state, and memory topology vary by host.

## Metrics and Acceptance

Record CPU-phase and GPU-phase process RSS plus the maximum of those values and
the sampled process high-water RSS in KB. On Linux, `rss_source=procfs` means
the values came from `/proc`, not a guessed constant.
Record communication separately from device execution and include it in every
row's `total_us`. Preserve the raw receipt and command stdout with the run.

Acceptance is `pass` only when all of the following hold:

1. The existing helper self-test exits zero.
2. At least three measured batch rows exist with warmup and sample counts above.
3. Every row satisfies `total_us = device_us + transfer_us`.
4. The first GPU-faster row is the recorded break-even batch.
5. At least one lower batch is non-faster and is assigned to CPU.
6. RSS and communication fields are present and measured.
7. An unavailable host has a typed `status=unavailable` receipt with a
   non-empty reason, and it is never counted as a measurement pass.

## Ownership

Linux owns the CUDA/Vulkan ProcessingIR producer, native receipt generation,
and this system spec. Linux verification must run on the target host with its
real driver and retain the receipt; CI without a device is a failure for this
evidence lane, not a synthetic pass.

macOS owns the postponed Metal live producer and host execution. It should
reuse this schema with `processing_ir_offload_backend=metal` only after the
Metal shader/queue/readback gate is live. macOS source/host contracts may be
checked separately, but they do not satisfy the Linux CUDA/Vulkan measurement.
