# Host/GPU Lane Requirements

Feature: `host_gpu_lane`

## REQ-001: Canonical Lane Grammar

Simple must accept the canonical host/GPU lane marker placement after
`later(...)` and before the existing lambda grammar:
`target.later(...) gpu \:` and `target.later(...) host \:`.

## REQ-002: Host Semantic Ownership

Host lane callbacks must remain the only lane allowed to commit host-owned UI
semantic state such as widget values, focus, layout truth, accessibility, text
input, and session state.

## REQ-003: GPU Batch Ownership

GPU lane callbacks must represent render/effect/resource acceleration through
coarse batches such as Draw IR deltas, DisplayGraphIR passes, dirty tiles,
resource uploads, animation batches, or hit-test batches.

## REQ-004: Host/GPU Diagnostics

The lane contract must reject GPU callbacks that mutate host semantic state and
must diagnose per-widget GPU dispatch that should be batched.

## REQ-005: Performance Evidence

Host/GPU lane evidence must record baseline CPU time and estimated or measured
GPU batch time, and the accelerated path must be lower in milliseconds when a
strict backend is available.
