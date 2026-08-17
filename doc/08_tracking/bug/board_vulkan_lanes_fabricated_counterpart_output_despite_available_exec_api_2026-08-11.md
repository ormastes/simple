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

---

## 2026-08-17 — measured re-audit on a real-GPU host: two of four unblock items are ALREADY DONE, and a NEW fail-open was found

This doc's problem statement is now partly stale, and its 2026-08-17 triage
("some of these lanes cannot produce genuine counterpart evidence on this host at
all") is wrong about the host. This machine has two real NVIDIA GPUs (RTX A6000
49140 MiB, TITAN RTX 24576 MiB, driver 580.126.16), a working Mesa lavapipe ICD,
and the Khronos SPIR-V tools installed. Each unblock item re-checked against
source and host:

| # | Unblock item | Measured status 2026-08-17 |
|---|--------------|----------------------------|
| 1 | SPIR-V via `glslangValidator`/`spirv-val` | **DONE.** `boundary_spirv_khronos_provider.spl:27,52,55` calls `process_run_bounded` against pinned `/usr/bin/spirv-as` and `/usr/bin/spirv-val` (present on host, `SPIRV-Tools v2025.1`), returns `ProviderStatus.unavailable` at line 165 when the tools are absent. Not fabricated. |
| 2 | Enumeration via `vulkaninfo` | **DONE.** `boundary_enumeration_provider.spl` now shells out (`shell("VK_ICD_FILENAMES=/usr/share/vulkan/icd.d/lvp_icd.json vulkaninfo …")`) and parses the real transcript in `parse_vulkaninfo_lavapipe`, failing closed to nil. The "hand-typed literal for lavapipe at lines 104-137" described above **no longer exists**. Verified the command produces real output here: `deviceName = llvmpipe (LLVM 20.1.2, 256 bits)`, `apiVersion = 1.4.318`. |
| 3 | Readback via a real lavapipe render | **STILL OPEN.** `boundary_readback_lavapipe_provider.spl` is 93 lines of manifests only — zero `shell(` / `process_run` calls. It remains descriptor-only, exactly as this doc described. |
| 4 | Independence groups | **OPEN, and worse than filed — see below.** |

### New finding: the independence gate is fail-open on its grouping key

`independence_gate_executed_group_count`
(`src/os/drivers/gpu/board_vulkan/provider_nvidia.spl`) is documented to group
executed sources by `SourceResult.independence_group` — that field is the entire
reason the Mesa family (anv/lavapipe/radv/nouveau/asahi/venus-guest) collapses to
one reference. The body instead groups by `source.provider_id`:

```
if source.provider_id != "":
    ... groups.push(source.provider_id)
```

Since `mesa_reference_source(id, …)` builds `provider_id = "host-mesa-" + id`,
six Mesa ICDs carry six distinct `provider_id`s and the gate counts them as
**six independent references**. Relabelling NVIDIA's `independence_group` into
`"mesa"` — the exact sabotage `nvidia_independent_reference_gate_spec.spl`
sabotage (a) exists to catch — leaves `provider_id` untouched and so still passes.
The candidate's deliberately-empty `independence_group` is likewise ignored, and
its `provider_id` counts as a group of its own.

This is the same defect class as the fabrication this doc reports: a gate that is
internally consistent and green while measuring something other than what it
claims. It makes every "two independent references" verdict this lane has issued
unsound.

Reproducing spec: `test/01_unit/os/vulkan/independence_group_key_regression_spec.spl`
Similar-problem detection spec: `test/01_unit/os/vulkan/independence_gate_key_confusion_detection_spec.spl`
(the detection spec pins the key rather than the counts, via a collapse property —
one family with many identities must count 1 — paired with a separation property —
one identity across two families must count 2; no identity-keyed implementation
can satisfy both.)

Both specs were committed RED-first in `a046b58ebc7`, then the fix landed in
`7709144473e`. Reproduce-first evidence, both verdict lines quoted verbatim from
`bin/simple test <spec> --timeout 800`:

**Before the fix** (reproducer, at `a046b58ebc7`):

```
    assert_false failed: got true
    assert_false failed: got true
    assert_false failed: got true
3 examples, 3 failures
SPEC FILE VERDICT: test/01_unit/os/vulkan/independence_group_key_regression_spec.spl declared>=3 executed=3 passed=0 failed=3 dropped=0
Results: 3 total, 0 passed, 3 failed
```

All three failures are `assert_false` on `independence_gate_satisfied(...)` — the
gate reporting independence SATISFIED where it does not hold, i.e. failing in the
fail-open direction, exactly as predicted from the source read.

**After the fix** (`7709144473e`, all three specs in one run):

```
SPEC FILE VERDICT: test/01_unit/os/vulkan/independence_group_key_regression_spec.spl declared>=3 executed=3 passed=3 failed=0 dropped=0
Results: 3 total, 3 passed, 0 failed
SPEC FILE VERDICT: test/01_unit/os/vulkan/independence_gate_key_confusion_detection_spec.spl declared>=3 executed=3 passed=3 failed=0 dropped=0
Results: 3 total, 3 passed, 0 failed
SPEC FILE VERDICT: test/01_unit/os/vulkan/nvidia_independent_reference_gate_spec.spl declared>=5 executed=5 passed=5 failed=0 dropped=0
Results: 5 total, 5 passed, 0 failed
```

The third file is the lane's own pre-existing spec, deliberately included in the
re-run. Its sabotage (a) asserts `independence_gate_executed_group_count == 1`
for a selection the provider_id-keyed gate necessarily counted as 3, so that
spec was RED on `main` for as long as the defect existed (deduced from the same
source read — its pre-fix verdict was not separately captured, because the run
attempting it was killed by an outer `timeout 900` before emitting one).

**The fix** (`src/os/drivers/gpu/board_vulkan/provider_nvidia.spl:200-217`): key
on `source.independence_group` instead of `source.provider_id`, and skip the
empty group so the candidate's deliberately-blank group can never count as an
independent reference.

Recorded here because it cost this session an hour and will cost the next one the
same: `scripts/check/check-test-verdict-not-silent.shs` printed

```
  OK  test/01_unit/os/vulkan/independence_group_key_regression_spec.spl
```

for the reproducer, and **that `OK` is not a pass.** That guard classifies only
*silence* — whether a run emitted any verdict/counts line at all. Its own
selftest (lines 97-103) feeds it fixture 4, `Results: 4 total, 3 passed, 1
failed` with exit 1, and requires the classification `OK` (`red:OK`). So `OK`
covers GREEN and honest RED identically and can never distinguish them. Only an
explicit `Results: N total, N passed` line settles a spec's outcome; a bare `OK`
from that wrapper must never be quoted as evidence that a spec passed.

Host conditions for the record: a stage-3 self-host build was live with ~174
concurrent `simple` processes, `bin/simple` currently resolves to the Rust
bootstrap seed (it says so on startup), and a single spec run took roughly an
hour to reach its first output.

Status: OPEN. Items 1 and 2 are closed by measurement; item 3 is unchanged; item
4 is now a concrete, specified, spec-covered code defect rather than a lane-rework
task.
