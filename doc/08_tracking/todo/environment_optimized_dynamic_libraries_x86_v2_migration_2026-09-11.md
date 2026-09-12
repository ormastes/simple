# TODO: Complete x86 V2 environment producer migration and qualification

**Status:** Open
**Owner:** compiler/runtime environment-variant integration lane
**Final reviewer:** independent x86 runtime and compiler verifier
**Affected criteria:** REQ-002, REQ-004, REQ-005, REQ-010, NFR-001, NFR-010

## Completed in the E2 candidate

- The baseline x86 snapshot helper and live CPUID adapter emit exact V2 feature
  words; hardware, OS usability, and policy ceilings remain separate.
- Canonical x86 publication fails closed through exact baseline/v3/v4 admission
  before artifact admission or mapping.
- AVX-512 usability requires XSAVE, OSXSAVE, and XCR0 bits 1, 2, 5, 6, and 7.
- Plain v4 remains separate from optional VBMI and VBMI2 variants.
- Device facts survive the x86 gate and malformed device ranges fail closed.

## Remaining migration and evidence

Inventory out-of-tree/product catalog builders and old fixtures before they
enter canonical publication. Replace legacy V1 x86 feature words with registry
V2 baseline/v3/v4 words as one atomic snapshot, descriptor, and policy-ceiling
migration. Do not add a generic-selector fallback for words missing the V2 tag;
that would bypass exact x86 admission.

Wire `compiler_host_environment_snapshot_x86_live_v1` from the product startup
composition root when an authenticated parser candidate is configured. Retain
`target_cpu` and `target_cpu_features` solely for generated output. Qualify the
result on physical x86-64 v2/v3/v4 hosts (including AVX-512-disabled OS state),
and retain CPU/device identities and environment generation in evidence.

## Unblock condition

Every product snapshot/catalog producer entering canonical x86 publication is
V2, the startup composition calls the live adapter without initializing an
optional GPU service, and qualified physical-host evidence proves correct
selection, required failure, preferred fallback, maximum ceilings, and no
wrong-ISA execution.
