# A hardware-gated spec whose only example is `skip_if`-skipped reports file-level FAIL, not SKIP

**Date:** 2026-08-11
**Found by:** two lanes writing forward-looking hardware-gated system specs, independently
**Severity:** Medium — undermines the whole point of "write the test now, it goes green when hardware lands"

## Symptom

Four new specs under `test/03_system/os/vulkan/` each contain exactly one `it`
block gated by `skip_if(condition, reason)` where `condition()` is currently
true (no matching hardware/build present). The `it`-level output correctly
shows the skip and the reason text, e.g.:

```
it proves the Gen12 encoder against real i915 hardware, not just self-comparison
  ... skipped (No Intel i915 GPU present on this host — see
  doc/08_tracking/bug/cmdstream_boundary_no_intel_gpu_on_capture_host_2026-08-11.md)
```

But `bin/simple test <spec>` reports the FILE-level verdict as:

```
Results: 1 total, 0 passed, 1 failed
reason=zero-examples
```

A skipped example is counted as `executed=0`, and the runner's zero-examples
guard — which exists to catch a genuinely broken spec that loaded but ran
nothing — cannot distinguish that from "the one example present was correctly
skipped by design". Both look identical from outside: one example declared,
zero executed.

## Why this matters here specifically

This affects a family of specs whose entire purpose is: exist today in a
harmless SKIP state, and flip to a real PASS with zero code changes the day
specific hardware or a build flag becomes available
(`board_vulkan_intel_gen12_submit_readback_system_spec.spl`,
`board_vulkan_adreno_submit_readback_system_spec.spl`,
`board_vulkan_img_bxe_submit_readback_system_spec.spl`,
`board_vulkan_venus_qemu_submit_readback_system_spec.spl`). A file-level FAIL
sitting in the tree reads as "this test is broken", not "this test is
correctly waiting for hardware" — which is the opposite of the intent, and
would mislead anyone scanning for red specs into treating a deliberate,
documented gate as a regression.

## Scope

Confirmed on 4 new files plus at least one pre-existing sibling using the
identical single-`it`-plus-`skip_if` shape, so this is a general runner gap,
not specific to these four files.

## Unblock condition

The test runner should treat "declared == 1, executed == 0, all-skipped == 1"
as a distinct, non-failing verdict (e.g. `SKIPPED`) rather than folding it into
the same `reason=zero-examples` bucket used for a spec that loaded but
genuinely ran nothing due to a defect. The two cases are semantically opposite
(intentional deferral vs. accidental no-op) and should not share one failure
code. A spec with N>1 examples where some are skipped and at least one executes
already reports correctly — this is specific to the all-skipped, N=1 case.

## Status

Open. Filed rather than worked around: the four hardware-gated specs are left
as written (correct `it`-level skip behavior, correct reason text) since
rewriting them to dodge this runner quirk (e.g. padding with a dummy always-run
example) would obscure their actual purpose. The file-level FAIL is a known,
accepted cosmetic issue until the runner is fixed.
