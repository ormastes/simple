<!-- codex-research -->
# Feature Requirement Options: Harden TUI/GUI Layout Comparison

## Option 1: Comparison Semantics Hardening

Description: Fix current comparison defects, make threshold/profile pass semantics explicit, preserve capture failures, and improve TUI spec diagnostics.

Pros: Smallest implementation path; directly addresses reachable defects; low risk to renderer architecture.

Cons: Does not add a full structural TUI/GUI layout comparison model; GPU/backend optimization remains mostly documented and gated.

Effort: M, about 4-8 files.

## Option 2: Structural Layout Contract Plus Pixel Diff

Description: Add a shared layout comparison contract that records TUI cell boxes and GUI pixel boxes, compares structure before pixels, and emits actionable mismatch reports plus existing screenshot diffs.

Pros: Best alignment with "harden tui and gui layout comparison"; reduces flaky pixel-only failures; creates durable design surface for future renderers.

Cons: Requires new fixtures/specs and adaptation across TUI and GUI paths; more design and test work.

Effort: L, about 10-18 files.

## Option 3: Full Backend Evidence Matrix

Description: Implement Option 2 and add backend-qualified evidence lanes for Metal, Vulkan, CUDA, and SIMD CPU with availability probes, benchmark manifests, artifact reporting, and fail-closed unavailable states.

Pros: Closest to full request; makes performance claims auditable; prevents false GPU acceleration claims.

Cons: Hardware coverage may be unavailable in this environment; highest maintenance cost; implementation may need follow-up tracking for unavailable platforms.

Effort: XL, about 18-35 files plus platform evidence runs.

## Option 4: Performance-First Backend Refactor

Description: Prioritize backend packaging, binary size, startup, and GPU/SIMD hot path optimization before expanding layout comparison semantics.

Pros: Attacks size/perf directly; useful if binary bloat or slow startup is the primary pain.

Cons: Misaligned if comparison correctness is the immediate blocker; optimization before clear comparison contracts risks weak evidence.

Effort: L/XL, about 12-30 files depending on selected backends.
