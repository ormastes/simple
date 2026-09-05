# Host/GPU Lane NFR Requirements

Feature: `host_gpu_lane`

## NFR-001: Grammar Simplicity

The feature must not introduce a second lambda grammar. `\:` and `\e:` remain
the lambda forms; `gpu` and `host` are lane markers.

## NFR-002: Fail-Closed Evidence

Strict GPU mode must not silently fall back to CPU. Any unavailable backend must
produce explicit fallback evidence.

## NFR-003: Hot-Path Batching

Hot-path GPU work must avoid per-widget dispatch and prefer frame/resource
batches to limit queue overhead.

## NFR-004: Documentation Traceability

Research, plan, design, executable SSpec, generated manual, guide, and skill
updates must reference the same canonical grammar.
