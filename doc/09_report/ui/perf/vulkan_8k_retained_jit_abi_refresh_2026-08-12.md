# Vulkan 8K retained JIT ABI refresh — 2026-08-12

Status: JIT ABI PASS; VULKAN SESSION BLOCKED.

The retained benchmark targets 7680x4320 with one changing 64x64 region, 10
warmup frames, and 200 measured frames. It requires exact transfer receipts,
p50/p95, RSS, checksum, fallback/completion state, and device identity.

## Change and verification

Two co-compiled `Engine2DReadback` declarations had diverged. The
`nogc_async_mut` mirror now includes `device_identity` and exposes the same
explicit identity construction path. The focused mirror ABI contract passes
2/2. Strict JIT no longer reports an uninferable `device_identity` field,
falls back to the interpreter, or attempts the prior 2.1 GB allocation.

## Remaining blocker

Using `/usr/share/vulkan/icd.d/lvp_icd.json`, the strict-JIT benchmark exits
cleanly before frame execution with:

```text
VULKAN_8K_RETAINED status=unavailable reason=Vulkan shared session initialization failed: availability
```

There is no p50, p95, RSS, frame checksum, or end-to-end transfer receipt from
this attempt. Existing lavapipe packed-strided transfer timing remains only
primitive-level evidence. This result does not establish dynamic 8K/80,
swapchain presentation, physical-GPU performance, or cross-device readiness.

## Provider refresh

Further tracing proved that the executable's zero-return Vulkan stub shadowed
the explicitly selected dynamic runtime. Runtime-provider precedence was fixed
and covered by a focused 1/1 unit test. A non-deploying Vulkan-enabled runtime
and compiler build completed successfully.

The refreshed strict-JIT attempt then failed closed on missing provider closure
for `rt_process_run_owned_bounded_value`, which is owned by the separate C
hosted runtime. No interpreter fallback occurred. This advances the blocker
from false Vulkan unavailability to an exact runtime-composition requirement,
but still produces no frame timing and no 8K/80 evidence.

## Composed-provider and bounded-seed result

The existing process-owner C source was built as an isolated provider and
preloaded beside the Vulkan-enabled runner. Exact SHA-256 identities were:

- runner: `392763f612b7de1481b9c6f67fb4392b631df30456bf7cc050d38693379fb951`
- Vulkan runtime: `e0cfe098330e779e66af400ffaecdd91053a5680f02ddd2252c6277630c0edc7`
- process owner: `1ef80a2475ab50be62e01b64b5f9478e7ee1b191765144ab16ae488480b005d5`

This composition initialized lavapipe and completed the first 8K compute
dispatch. A monolithic 132.7 MB mirror seed returned a byte-count mismatch;
31.5 MB strided seed strips reached the transfer path but crashed in packed
array conversion. The benchmark now seeds with exact 64-row, 1.97 MB strips.
That strict-JIT run completed with exit 0 through all warmup/timed dispatches,
with no observed CPU-fallback or completion-unknown trace.

Verbose Vulkan ordering diagnostics exceeded the captured output budget and
the final `VULKAN_8K_RETAINED` row was not retained. Therefore this is execution
progress, not admissible performance evidence: p50/p95, RSS, transfer totals,
and checksum remain unrecorded. Per the three-cycle guard, the benchmark was
not repeated. The next fresh run must disable ordering trace and redirect the
single result row to a file before deciding the 8K/80 gate.

## Captured timing and proof failure

A fresh file-captured run retained these short receipt records:

```text
status=pass viewport=7680x4320 frames=200
p50_ns=1040146 p95_ns=1539488 target_p95_ns=12500000 rss_kb=0
calls=200 bytes=3276800 expected_bytes=3276800 full_fallbacks=0
cpu_fallback=false completion_unknown=false sampled_checksum=0
```

The timing and transfer gates pass narrowly, but RSS and checksum evidence are
invalid. The harness was tightened to require first/damage/last pixel parity
and a nonzero sampled checksum. That run completed the timed frames and then
SIGSEGVed during the sample phase; external GNU time measured peak RSS
2,137,920 KiB. The ordering trace also remained enabled even with its variable
removed, indicating split runtime environment state in this composed runner.

Consequently Vulkan retained 8K/80 remains **UNPROVEN**, despite the measured
1.54 ms p95. The authoritative blocker is tracked in
`doc/08_tracking/bug/vulkan_8k_jit_retained_host_buf_sample_crash_2026-08-12.md`.

## Physical class identity hardening

The retained Engine2D backend and the Skia Vulkan translator previously shared
the physical class name `VulkanBackend`. Because strict JIT compilation has a
flat class registry, the Skia implementation now uses the physical name
`SkiaVulkanBackend` while exporting `VulkanBackend` as a compatibility alias.
Direct retained-field sampling also avoids materializing the 8K mirror into a
second local array.

The next evidence attempt was deliberately stopped before benchmark execution:
it remained in compilation while unrelated high-memory Simple builds were
active, emitted no `VULKAN_8K_RETAINED` receipt, and left the GNU-time file
empty. No timing or 8K/80 conclusion is drawn from that attempt.
