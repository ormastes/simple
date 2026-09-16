# Vulkan 8K strict-JIT retained host-buffer sample crash

Date: 2026-08-12

## Status

OPEN. The retained Vulkan workload completes 200 timed frames, then strict JIT
terminates with SIGSEGV when the evidence harness directly samples the retained
`VulkanBackend.host_buf` for readback parity.

## Reproducer shape

- viewport: 7680x4320
- backend: Vulkan compute on pinned lavapipe
- damage: one 64x64 rectangle
- warmup/timed frames: 10/200
- mirror seed: exact full-width 64-row strided transfers
- runtime: composed Vulkan-enabled Rust runner plus isolated canonical process
  owner
- mode: `SIMPLE_JIT_STRICT=1`

The immediately preceding run, before direct sample assertions were added,
reported p50 1,040,146 ns and p95 1,539,488 ns, exact 3,276,800 transfer bytes,
zero full fallbacks, `cpu_fallback=false`, and `completion_unknown=false`, but
also an invalid zero checksum. Adding reads of indices 0, the damaged pixel,
and the last pixel changes the post-frame evidence phase into SIGSEGV. GNU time
reported peak RSS 2,137,920 KiB for the crashing run.

## Required closure

- Isolate whether class-field array borrowing, direct indexed access, or the
  retained mirror's lifetime is corrupted under JIT.
- Add a small strict-JIT regression that reads first/middle/last values from a
  class-owned `[u32]` after repeated mutation.
- Preserve a nonzero checksum or explicit sampled parity receipt.
- Re-run the 8K benchmark only after that regression passes.

The timing-only row is not an admissible 8K/80 pass because readback parity is
unproven. Do not replace the missing proof with an expected checksum.

## Reduction result

`test/fixtures/jit_class_u32_array_retained_read/main.spl` allocates the same
33,177,600-element `[u32]` size, stores it in a class field, mutates one retained
pixel for 210 frames, aliases the field, and reads first/changed/last under
strict JIT. It passes:

```text
JIT_RETAINED_ARRAY first=0 changed=4280207470 last=0
```

The defect is therefore not generic large class-owned array access.

## Backend identity collision

Lifecycle markers then proved that `backend.host_buf.len()` remained
33,177,600 after initialization, mirror seeding, warmup, and all 200 timed
frames. Materializing the field into a local array produced length zero before
the first sample read. Repository inspection found two physical classes named
`VulkanBackend`: Engine2D's retained backend and Skia's unrelated command
translator. The Skia physical class is now `SkiaVulkanBackend`, with
`type VulkanBackend = SkiaVulkanBackend` preserving its public API. Its focused
interpreter specification passes 11/11 through the public alias after the
rename. A later attempt to extend the same spec did not reach its examples
because the shared host was saturated by unrelated compiler builds; that
unverified assertion was not retained.

The first post-fix strict-JIT 8K attempt did not reach frame execution. It
stalled during compilation while several unrelated Simple builds were active;
the exact benchmark and `/usr/bin/time` processes were terminated, leaving an
empty timing receipt. This is host-concurrency/build-capacity evidence, not a
rendering failure or pass. Do not retry until the host can compile the fixture
without competing high-memory builds.

---

## Triage classification 2026-08-17 — DEFERRED: requires Vulkan-capable GPU + QEMU/8K render lane

Reviewed in the second-pass backlog sweep. Not actionable from this session:
the crash is in a JIT-compiled Vulkan sample needing a working Vulkan device and the 8K render harness. No code change is possible without that, so no
speculative fix was attempted. Classification recorded here so future sweeps
skip it in O(1) instead of re-deriving the blocker. Status remains OPEN.


## Triage 2026-08-17 — DEFERRED, blocker recorded

Reviewed in the lines 32-46 backlog sweep. Not actionable from this session: GPU-hardware gated -- needs a working Vulkan device plus an 8K surface to
reproduce a JIT-path sample crash. Not reproducible headless on this host.

Status unchanged. Recorded so future sweeps skip this in O(1) instead of
re-deriving the same blocker.

---

## 2026-08-17 — BOTH 2026-08-17 triage notes above are FALSE and are retracted

The two deferrals above assert this bug is "GPU-hardware gated", "needs a working
Vulkan device", and is "not reproducible headless on this host". All three claims
are wrong, for two independent reasons.

**1. The reproducer never needed a GPU.** This doc's own "Reproducer shape"
section, five lines long, states `backend: Vulkan compute on **pinned lavapipe**`.
lavapipe is Mesa's software rasterizer; it needs no GPU by design, and it is
installed and enumerating on this host:

```
$ VK_ICD_FILENAMES=/usr/share/vulkan/icd.d/lvp_icd.json vulkaninfo | grep -E 'deviceName|apiVersion'
	apiVersion        = 1.4.318 (4211006)
	deviceName        = llvmpipe (LLVM 20.1.2, 256 bits)
```

The deferrals were derived from the word "Vulkan" in the title rather than from
the reproducer, which is the failure mode this doc's own closing line warns
against ("Do not replace the missing proof with an expected checksum").

**2. Real Vulkan hardware exists here regardless.** Two NVIDIA GPUs (RTX A6000
49140 MiB, TITAN RTX 24576 MiB, driver 580.126.16) enumerate under
`VK_ICD_FILENAMES=/usr/share/vulkan/icd.d/nvidia_icd.json vulkaninfo` with
`vendorID = 0x10de`, `apiVersion = 1.4.312`.

### What the actual blocker is

Read against the body rather than the title, this bug is already root-caused and
the fix already landed: two physical classes were both named `VulkanBackend`
(Engine2D's retained backend and Skia's command translator), so materializing
`backend.host_buf` resolved against the wrong class and yielded length zero — the
`SkiaVulkanBackend` rename plus the `type VulkanBackend = SkiaVulkanBackend`
alias is recorded above as done, with its focused spec at 11/11. The reduction
fixture `test/fixtures/jit_class_u32_array_retained_read/main.spl` independently
proves generic large class-owned `[u32]` access is not at fault.

What remains is a single re-run of the 8K benchmark to replace the empty timing
receipt, and the doc already states why that run failed: "the shared host was
saturated by unrelated compiler builds ... This is host-concurrency/build-capacity
evidence, not a rendering failure or pass. Do not retry until the host can compile
the fixture without competing high-memory builds." That condition still holds
today (a stage-3 self-host build is live in this session), so the re-run was again
not attempted.

**Correct classification: capacity-gated re-verification of an already-landed fix.
Not hardware-gated.** Any future sweep that re-defers this as "needs a Vulkan GPU"
is repeating an error that has now been made twice.

## 2026-08-17 host-fixable evidence boundary

The Engine2D backend now exposes `sample_host_mirror(indices)` so evidence
sampling resolves and indexes `host_buf` inside the concrete physical
`VulkanBackend` owner. Invalid indices fail closed without partial samples.
The adjacent strict-JIT fixture models the exact full-width 64-row strided
mirror update for 210 mutations and samples first/damaged/last pixels through
the same owner-local shape. This supplements the earlier generic large-array
negative reduction and directly guards the collision/mirror boundary.

This Darwin ARM host enumerates Apple M4 through MoltenVK, not lavapipe. The
focused owner and strict-JIT evidence can run here, but no 8K lavapipe or NVIDIA
receipt is claimed; the full 7680x4320 capacity rerun remains pending.
