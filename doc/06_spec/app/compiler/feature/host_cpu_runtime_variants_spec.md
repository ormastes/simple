# Host CPU Runtime Variants Spec

Executable artifact:
- `doc/06_spec/app/compiler/feature/host_cpu_runtime_variants_spec.spl`

## What The Executable Spec Covers

- The `.spl` file is now a behavioral model, not a literal checklist. It executes input/output scenarios for:
  - active-tier precedence: override, then `cpu_config.sdn` `enabled.simd_tier`, then detection
  - enabled instruction-set clamping to `support ∩ simple_support` in canonical order
  - runtime-library probe ordering and implemented-tier collapse
  - embedded package runtime fallback when the highest compatible metadata entry is missing
  - fail-closed manifest validity rules for truncated or malformed trailing metadata
  - cache identity changes and stdlib variant-root ordering changes when the active tier changes

## Honest Scope Boundary

- This spec layer does not have a repo-exposed Simple API for the Rust internals that actually parse SDN, load dynamic libraries, or read package manifests.
- Because ownership for this follow-up is limited to the spec files, the executable `.spl` models the required behavioral contract rather than directly invoking the Rust implementation.
- The real implementation evidence for those same rules remains in the Rust tests across `simple-simd`, `simple-native-loader`, `simple-runtime`, `simple-compiler`, `simple-driver`, and the mirrored package readers.

## Requirement Traceability

- `REQ-001` to `REQ-004`: modeled in the executable spec and implemented in `simple-simd` host config tests for path override, precedence, and first-use config behavior.
- `REQ-005` and `REQ-006`: modeled in the executable spec and implemented in `simple-simd` canonicalization tests for rewrite, dedupe, and clamp semantics.
- `REQ-007`: modeled in the executable spec and implemented in `simple-native-loader` plus interpreter dynamic-loader tests for sibling probe order, default search-path behavior, and fallback handling.
- `REQ-008` and `REQ-009`: modeled in the executable spec and implemented in loader/runtime package tests for `runtime_variants` round-trip, fail-closed manifest parsing, and embedded-resource fallback.
- `REQ-010`: modeled in the executable spec and implemented in compiler and driver cache-key tests keyed by active SIMD tier.
- `REQ-011`: modeled in the executable spec and implemented in compiler stdlib-root and path-resolution tests driven by `cpu_config.sdn`.
- `REQ-012` and `REQ-013`: modeled in the executable spec and implemented in runtime-variant selection tests covering the v1 matrix and collapse through implemented fallback tiers.

## Residual Limitation

- This file no longer claims end-to-end executable verification of the Rust implementation from SSpec alone.
- If the repo later exposes a Simple-facing API for host-config parsing, package manifest loading, or runtime variant selection, the `.spl` should be upgraded from contract-model scenarios to direct system calls against that API.
