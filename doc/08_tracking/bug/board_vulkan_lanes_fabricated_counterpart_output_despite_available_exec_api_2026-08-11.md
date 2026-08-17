# Board-Vulkan lanes compared against fabricated counterpart output while a process-exec API existed

**Filed:** 2026-08-11
**Found by:** parent review of eight parallel boundary lanes + red-team audit
(`doc/09_report/board_vulkan_lane_redteam_audit_2026-08-11.md`)

## Problem

Not one of the board-Vulkan boundary lanes actually executed an open-source
counterpart. Every "comparison" ran against bytes authored by the lane itself:

- **L2 device enumeration** — `boundary_enumeration_provider.spl:104-137` returns a
  hand-typed literal for lavapipe. Nothing invokes `vulkaninfo`. Caught by the
  audit, which correctly rated the lane WEAK: it tests the comparator, not Simple
  against Mesa. The expected side has no independent origin, which is the
  expected-from-actual trap in its most direct form.
- **L3 readback** — declared honestly by the lane itself: lavapipe is a descriptor
  only, nothing invokes `libvulkan_lvp.so`, and image bytes are caller-supplied
  strings. The receipt gate it built is genuinely sound and sabotage-proven; there
  is simply no end-to-end pixel comparison behind it.
- **L4 provider inventory** — the measured hashes and versions are real, but they
  were gathered out-of-band by the agent's own shell, not by the spec. L4
  explicitly reported that implementing host-derived verification "needs a
  verified process-exec capability from pure Simple, which wasn't
  available/verified within this lane's scope."

## The reason that conclusion was wrong

The capability exists and is exported from the stdlib:

- `src/lib/nogc_sync_mut/io/process_ops.spl:76`
  `pub fn process_run_bounded(cmd: text, args: [text], timeout_ms: i64, max_output_bytes: i64) -> (text, text, i64)`
- `src/lib/nogc_sync_mut/io/process_ops.spl:414`
  `pub fn process_run_with_limits(...) -> ProcessResult` (timeout, memory, CPU, fd
  and subprocess caps — the bounded form a test lane should prefer)
- `src/lib/nogc_sync_mut/io_runtime.spl:170` `pub fn process_run(cmd, args)`
- `src/lib/common/spec/evidence/format/exec_capture.spl:142` `exec_to_evidence(...)`
  already projects a captured execution into canonical evidence — i.e. the
  evidence path for "I ran a foreign binary and captured its output" is built.

So no lane needed to fabricate a counterpart side. `process_run_bounded` with a
timeout and an output cap is exactly the shape a counterpart provider wants.

## Why this matters more than any single lane's verdict

Every green verdict these lanes produced is a verdict about Simple's own data
structures. The stated purpose of the whole effort — compare Simple's IO against
the open-source counterpart's IO at each layer — is **not yet demonstrated at any
boundary**. The gates, canonicalizers, ledgers and independence predicates are
real and sabotage-proven; the comparison they wrap has one real side and one
authored side.

This is a fail-open of exactly the kind the counterpart plan's rule 11 forbids
("never create expected output from actual candidate output"), and it survived
because each lane's green run *is* internally consistent.

## Unblock condition

Per boundary, replace the authored counterpart side with a real execution:

1. **SPIR-V** (`vulkan.shader.spirv_binary@1`) — `process_run_bounded("glslangValidator", ["-V", "-o", out, src], …)`,
   then `spirv-val` on both sides. Needs no GPU; this is the cheapest first proof.
2. **Enumeration** (`vulkan.device.enumeration@1`) — `vulkaninfo` with
   `VK_DRIVER_FILES=/usr/share/vulkan/icd.d/lvp_icd.json` (lavapipe needs no GPU),
   parsed into the canonical record.
3. **Readback** (`vulkan.present.readback_image@1`) — a lavapipe render producing
   real reference pixels, not caller-supplied bytes.
4. **Independence groups** — `dpkg -S` on each pinned `.so`, asserting
   `declared == derived`, closing
   `board_vulkan_independence_group_is_unverified_declaration_2026-08-11.md`.

A provider that genuinely cannot run must report `ProviderStatus.unavailable` so
the run is rejected — never a literal that looks like a result.

## Status

Open. The infrastructure landed in `efa085ebc26` is kept: the receipt gate, the
arch-substitution guard, the provider inventory and the independence predicates
are sound and independently sabotage-proven, and they are what a real execution
will plug into. What is not yet true is any claim that Simple's Vulkan IO has been
compared against Mesa's.

## 2026-08-17 triage — remains OPEN; process/lane-rework finding, not a code defect

Re-read and left in place. This doc records that no board-Vulkan boundary lane
executed a real counterpart — the expected side was authored by the lane itself
(hand-typed lavapipe literals, caller-supplied image bytes, out-of-band shell
measurements). That is the expected-from-actual trap, and the SPipe contract is
unambiguous about it: a provider that cannot run reports
`ProviderStatus.unavailable` and the run is REJECTED, never fabricated.

Fixing it means rewriting those lanes to invoke `vulkaninfo` / `libvulkan_lvp.so`
through the process-exec API from inside the spec, plus a sabotage arm per lane
that turns green to red. That is lane feature work owned by the board-Vulkan
campaign, not a small verified diff, and this triage lane must not close it by
re-labelling. Note also that the sibling blockers re-verified today
(`cmdstream_boundary_no_intel_gpu_on_capture_host`,
`host_qemu_virtio_gpu_gl_missing_egl_symbol`) mean some of these lanes cannot
produce genuine counterpart evidence on this host at all — the honest end state
for those is `unavailable`, recorded and visible, never a synthesized pass.
