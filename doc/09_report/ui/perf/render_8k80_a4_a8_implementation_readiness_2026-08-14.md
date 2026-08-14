# Render 8K80 A4–A8 implementation readiness

Status: **WARN — software handoff implemented; live and physical evidence open**

This audit distinguishes implementation from performance evidence. It does not
promote a source check, fixture, CUDA inventory, Xvfb window, or source-buffer
checksum into an 8K80 result.

| Item | Implemented now | Evidence still unavailable |
|---|---|---|
| A4 | The canonical 7680x4320 CPU DrawIR benchmark, exact command counters, direct-native builder/runner, receipt normalization, provenance manifest, and deliberate-red validation exist. | A provenance-admitted self-hosted Stage 4 compiler must build and directly execute the carrier once (TODO686–688). |
| A5 | Canonical Web semantic lowering to DrawIR, strict Engine2D Vulkan submit/fence observation, untimed device readback, 1 warmup plus 60 timed samples, truthful exit status, and container execution exist. | The admitted compiler must build the native producer and a qualified Vulkan container must execute it (TODO810). |
| A6 | Physical X11/EDID/active-mode admission exists. A retained native producer executes the same A5 Web semantics through strict DrawIR/Vulkan visible-window presentation, transferring one Engine2D owner and validating completion, no admitted fallback/readback, stable identities, changing untimed device checksums, and 62 plus an explicit bounded untimed surface-seed count in observed submits/fences. | The producer must execute on physical hardware and its scanout must be independently captured/read back on the same device. The existing Rust window test hashes its source buffer; that is not physical-scanout capture and cannot satisfy A6 (TODO684/685). |
| A7 | The parent-authoritative fixed-schema aggregator, freshness/source/run/campaign/device correlation, immutable evidence manifest, blocked-physical state, physical promotion, and deliberate-red matrix exist. | Fresh admitted A4, A5, and physical receipts must be supplied together (TODO811). |
| A8 | Fail-closed connector inventory, readable EDID decoding, active 7680x4320 at 80 Hz-or-faster admission, and exact-run capture-receipt correlation exist. | No qualifying connector/mode or independent scanout capture is attached to this host; retain WARN until hardware is available (TODO685). |

The physical wrapper pins one immutable software run, verifies the cached
window artifact and aggregate-bound manifest, and publishes a successful
physical evidence set by atomic rename plus read-only permissions and an atomic
`current` link. Mutable caller files or a moving software `current` link cannot
become durable PASS evidence.

## Optimization review

No measurement-semantic shortcut is admissible. A4 intentionally measures its
CPU DrawIR retained-damage workload. A5 intentionally performs canonical Web
semantic/layout lowering for each changing revision before strict Vulkan
submission; caching pre-lowered DrawIR would measure a different workload.
Timed readback remains zero, final readback stays outside the timed interval,
and the backend-owner submit/fence delta prevents successful no-op work.

The remaining work is admitted execution and physical capture, not an
unimplemented rendering path. CUDA qualification proves container device access only; it neither
accelerates A4 nor substitutes for Vulkan presentation or physical scanout.

The safe build-time optimization is implemented: all three native entries share
one source-matched native-build cache, while their outputs and logs remain
separate and manifest-hashed. The required optimizer/check executable could not
load this source revision because `bin/release/simple` failed its bounded ABI
probe before parsing the new producer. No seed fallback was used, and no
optimizer/performance PASS is claimed.

## Exact unavailable-hardware check

Run the existing bounded parser/admission self-test first, then on the physical
host run:

```sh
DISPLAY=:0 VK_ICD_FILENAMES=/usr/share/vulkan/icd.d/nvidia_icd.json \
  sh scripts/check/check-render-perf-physical-8k80-hardware.shs
```

Exit 2 is the expected blocked result when the EDID-bearing 8K80 path is absent.
Full PASS additionally requires a same-run physical receipt accepted by
`scripts/check/check-render-perf-8k80-container.shs --aggregate`.

## CUDA/Vulkan container preparation update

The runner now explicitly exposes NVIDIA compute, utility, and graphics
capabilities and retains `nvidia-smi` plus `vulkaninfo --summary` inventory.
CUDA is admitted only by its generated submit/readback checker. Vulkan is
admitted separately by the strict A5 semantic producer with selected backend
`vulkan`, known completion, device readback, no fallback, zero timed readback,
and p95 at most 12.5 ms. The bounded contract rejects over-budget A4 and A5
receipts. Live performance remains blocked on the admitted Stage4 compiler;
the deployed runtime failed its bounded ABI probe before loading the new SSpec.
