# Bootstrap SDK Capsule Contract

This document defines the preparatory contract for a portable bootstrap SDK
capsule. It is architecture preparation only. A passing contract check does
not prove source reproducibility, Stage-4 admission, deployment, rollback, or
platform acceptance.

## Toolchain prerequisite

The first capsule authority must bind a Clang/LLVM 23.1 toolchain identity.
Its manifest records the exact `llvm-config`, `clang`, `llvm-as`, `opt`, and
`llc` versions and hashes. LLVM 18/20 artifacts are incompatible historical
diagnostics, not a valid capsule seed. The Rust seed's Inkwell/llvm-sys
binding must migrate before this prerequisite can be met.

Current staging evidence is deliberately weaker: a local LLVM 23.1.0-rc2
provider can expose all five tools and headers, and `aya-llvm-sys 231` links
against it under strict versioning. It is disposable host evidence only until
the provider is pinned into the capsule and Inkwell exposes a reviewed
`llvm23-1` feature.

## Goal

The capsule has exactly four shared interfaces:

1. `BootstrapSdkManifest` identifies the capsule schema, target, source
   identity, entry point, module set, and declared artifact digests.
2. `BootstrapSdkModuleInterface` describes the stable name, imports, exports,
   and ABI-relevant surface of one module.
3. `BootstrapSdkBodyArchive` stores the source bodies and per-body digests in a
   deterministic module order.
4. `BootstrapSdkProvenance` records the producing compiler, command, host,
   runtime bundle, source identity, and artifact digests.

The interfaces are data contracts. They do not replace source rebuilds of
`src/compiler/**`, and they must not be used to hide a Stage-3 or Stage-4
failure.

## SDK acceptance requirements

- `SDK-001`: the manifest interface is named and identifies the capsule.
- `SDK-002`: the manifest records target and source identity.
- `SDK-003`: the manifest declares the entry point and module set.
- `SDK-004`: module interfaces expose imports and exports.
- `SDK-005`: module interfaces include ABI-relevant surface information.
- `SDK-006`: body archives preserve deterministic ordering and body digests.
- `SDK-007`: provenance records compiler and runtime identity.
- `SDK-008`: provenance records command, host, and source identity.
- `SDK-009`: artifact digests are bound to the manifest and provenance.
- `SDK-010`: preparation explicitly excludes reproducibility, Stage-4
  admission, and platform acceptance claims.

## Contract helper

The executable contract helper is `step_bootstrap_sdk_contract`. It checks
the four canonical interface names, each `SDK-001` through `SDK-010`, and the
negative claim fields:

```text
reproducibility_evidence=false
stage4_admission_pass=false
platform_acceptance=false
```

The helper must reject the corresponding `true` markers. The negative checks
are written against explicit false fields and therefore do not contradict the
manual's explanation of the prohibited claims.

## Scenario labels

The architecture contract uses the same exact eleven labels as the executable
spec, manual, and system-test plan:

- `CAPSULE-001: canonical interfaces`
- `CAPSULE-002: manifest identity`
- `CAPSULE-003: target and source identity`
- `CAPSULE-004: entry point and modules`
- `CAPSULE-005: module imports and exports`
- `CAPSULE-006: ABI surface`
- `CAPSULE-007: deterministic body archive`
- `CAPSULE-008: compiler and runtime provenance`
- `CAPSULE-009: command host and source provenance`
- `CAPSULE-010: artifact digest binding`
- `CAPSULE-011: preparation claim boundary`

## Claim boundary

Contract preparation is complete only when the interfaces and traceability
are present. It is not evidence that a binary is reproducible, that x86
Stage 4 has passed, or that Linux AArch64, macOS, FreeBSD, SimpleOS, or any
other platform has been accepted. Those claims require their own source-bound
build, runtime, and retained-evidence gates after Stage-4 admission.

## Post-bootstrap acceptance interface

`scripts/check/check-post-bootstrap-stage4-sspec.shs BINARY BINARY_SHA256
PROVENANCE PROVENANCE_SHA256` is the read-only acceptance bridge. It binds both
exact input hashes, verifies adjacent v1 provenance, rejects noncanonical or
symlinked inputs, and proves retained smoke stayed unchanged.
