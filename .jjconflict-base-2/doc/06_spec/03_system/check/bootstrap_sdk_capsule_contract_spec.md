# Bootstrap SDK capsule contract

This manual describes the preparatory contract only. It does not claim source
reproducibility, Stage-4 admission, deployment, rollback, or platform
acceptance. The executable source is
`test/03_system/check/bootstrap_sdk_capsule_contract_spec.spl` and its shared
flow helper is `step_bootstrap_sdk_contract`.

## Contract flow

### CAPSULE-001: canonical interfaces

The contract names `BootstrapSdkManifest`, `BootstrapSdkModuleInterface`,
`BootstrapSdkBodyArchive`, and `BootstrapSdkProvenance`.

### CAPSULE-002: manifest identity

The manifest identifies the capsule schema and capsule instance.

### CAPSULE-003: target and source identity

The manifest binds the target and source identity used to prepare the capsule.

### CAPSULE-004: entry point and modules

The manifest declares the entry point and deterministic module set.

### CAPSULE-005: module imports and exports

Each module interface records its imports and exports.

### CAPSULE-006: ABI surface

Each module interface records the ABI-relevant surface needed by consumers.

### CAPSULE-007: deterministic body archive

The body archive preserves module order and a digest for every body.

### CAPSULE-008: compiler and runtime provenance

Provenance records compiler identity and runtime-bundle identity.

### CAPSULE-009: command host and source provenance

Provenance records the producing command, host, and source identity.

### CAPSULE-010: artifact digest binding

Artifact digests are bound to both the manifest and provenance records.

### CAPSULE-011: preparation claim boundary

The contract publishes these explicit fields:

```text
reproducibility_evidence=false
stage4_admission_pass=false
platform_acceptance=false
```

Inputs that attempt to set any of those fields to a true value are rejected.
The false fields are not evidence of a successful build or acceptance gate.

## Evidence boundary

This manual documents contract presence and traceability. It does not prove
reproducibility, x86 Stage-4 admission, deployment, rollback, Linux AArch64
or macOS bootstrap, FreeBSD QEMU bootstrap, SimpleOS bootstrap, or physical
board operation. Those outcomes require their own source-bound commands and
retained evidence after the Stage-4 gate.
