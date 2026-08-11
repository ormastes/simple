# Board Vulkan + SCCT — what was achieved, and what this host cannot do

**Date:** 2026-08-11
**Scope:** the effort begun from `doc/08_tracking/bug/simpleos_vulkan_board_gap_venus_is_qemu_only_2026-08-06.md`
**Pushed:** verified at `github.com/ormastes/simple` — all files below confirmed present at origin by path, not by exit code

This exists because the goal was "build an open-source Vulkan driver and compare it
with the SimpleOS Simple-written driver", and the honest answer has two halves: a
substantial amount was achieved, and one specific part is impossible here for
reasons that are now measured rather than assumed. Recording both so the next
person does not re-derive either.

## Achieved

| Goal clause | Outcome |
|---|---|
| Fix the venus-is-QEMU-only architecture gap | venus demoted to one `qemu_only` backend of a SoC-neutral core |
| Migrate the existing Vulkan impl | virtio/venus reclassified as B0; `spirv_builder` reused as the candidate |
| Adreno / StarFive VF2 / UP SBC in parallel | three real command-stream encoders, written concurrently, each sabotage-proven |
| Compare against an open-source counterpart | four boundaries; three execute a genuinely independent counterpart |
| SimpleOS driver stages | 1 of 3 earned — `spirv` proven, `submit`/`readback` blocked |

Real counterpart executions, each with a negative control:

- **SPIR-V** — Simple's module assembles under Khronos `spirv-as` (exit 0) and
  **validates** under `spirv-val` (exit 0), SPIRV-Tools v2025.1. Negatives: a bogus
  opcode is rejected (247); an undefined entry-point id passes `spirv-as` but is
  caught by `spirv-val` (1). That asymmetry is the lesson — assembling is not
  validating.
- **Device enumeration** — real `vulkaninfo` pinned to lavapipe, 17/17, sabotage
  red naming a dropped `HOST_CACHED` flag.
- **Digest** — Simple's SHA-256 vs real `openssl dgst` vs published NIST vectors,
  4/5 and 5/5 across two providers. Simple's implementation genuinely agrees with
  OpenSSL 3.0.13 and FIPS 180-4.
- **In-process dynlib** — `dlopen`'d `libcrypto.so.3` called directly, matched
  against NIST vectors, fail-closed on missing library or symbol.

Hardening that fixed real defects rather than decorating working code:

- the venus ICD **fabricated success** on every call (`is_ok: true` plus a real
  handle, with no device) — now fail-closed with typed Unavailable/Failed. Four
  pre-existing spec examples had been *asserting* the fabricated behaviour.
- Gen12's `total_dwords - 2` could **underflow and wrap** into a runaway GPU read;
  all three encoders now reject impossible input with a field-naming typed error.
- GPU probe availability was derived from `device_id > 0`, conflating "no device"
  with "device id 0".

## Impossible on this host, measured

| Blocker | Evidence |
|---|---|
| No Intel GPU | no real `anv` batch capture is possible regardless of tooling |
| No QEMU model for Adreno or IMG BXE | those in-guest device paths are board-only |
| QEMU cannot load `virtio-gpu-gl` | `undefined symbol: qemu_egl_display`; absent from the binary and all six opengl-module `.so` files; QEMU's own words: `opengl is not available`. `venus=on` is never evaluated — the failure is a layer below virgl/venus negotiation |
| No headless render binary | `vulkaninfo` does not render; `vkcube` needs a live DISPLAY and has no dump flag; no deqp/vkmark |
| No PowerVR kernel UAPI | the BXE envelope layout is our convention, not the verified ABI |

`submit` requires submitting to a device; `readback` requires reading pixels back
from one. Neither is reachable without one of: an Intel GPU, an Adreno board, a
VisionFive 2, or a QEMU built with working OpenGL. **This is a hardware and
packaging limit, not an effort limit** — no amount of additional work on this
machine changes it.

## Corrections made to our own claims

Worth listing, because each was believed before it was checked:

1. **`byte_exact` was the wrong relation for SPIR-V.** Two compilers legitimately
   emit different SPIR-V for the same source. The plan stated that rule correctly
   for compression and contradicted it for SPIR-V.
2. **venus's independence group was wrong** — Mesa's venus guest ICD is `mesa`, not
   `virglrenderer`. The old grouping would have double-counted references. Caught by
   two lanes disagreeing with the frame.
3. **A sabotage asserted that the fake had succeeded** and called it "caught". The
   independence group is an unverified declaration; a relabel silently inflates the
   count. Now derived from the host via `dpkg -S` and asserted.
4. **An aarch64 absence-claim was false** — an EDK2/AAVMF real-firmware record
   existed all along; the lane searched one directory. An absence check needs a
   control that must produce a hit.
5. **`process_run_bounded` works from a spec.** Three lanes concluded otherwise and
   substituted hand-authored literals for counterpart output.
6. **`reportedly fails` in a plan is not a finding.** That phrasing kept the venus
   blocker ambiguous for days until someone ran the command.

## Debt this effort created

- `check-directory-fanout.shs` FAILs: 7 directories over `structure.md`'s 10-file
  limit, three of them ours (`board_vulkan` ~20 files, `test/01_unit/os/vulkan`,
  `doc/08_tracking/bug`). Ours, not inherited.
- `SpirvBuilder` drops its whole module to the interpreter at ~100–1000× via
  unresolved JIT symbol `SpirvBuilder_dot_create`. Cost about four hours across two
  lanes; the SPIR-V evidence is a reproducible transcript but is **not CI-gated**
  until this is fixed.
- The revert guard cannot distinguish re-adding an upstream-deleted file from a
  revert — re-adding always matches the older blob.

## What would move this forward

In order of value per effort: fix the JIT symbol so the SPIR-V proof becomes
CI-gated; obtain a QEMU with working OpenGL, which revives the whole venus lane
including `submit` and `readback` in a VM; then real hardware for the three board
SoCs, which is the only route to a board-runnable claim.
