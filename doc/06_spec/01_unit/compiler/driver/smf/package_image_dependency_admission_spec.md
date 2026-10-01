# Package-image dependency metadata admission

**Status: authored manual; execution and SPipe generation pending.** No admitted
self-hosted runner was available when these scenarios were added. This file is
not generated test evidence and does not establish a passing acceptance gate.

Executable source: [package_image_dependency_admission_spec.spl](../../../../../../test/01_unit/compiler/driver/smf/package_image_dependency_admission_spec.spl).

The compiler's package-image validator checks the format of every dependency
digest before it admits metadata. A correctly hashed receipt containing the
same malformed value cannot replace this format check. The existing typed
`PackageImageErrorV1.invalid_checksum` identifies the refusal.

| Scenario | Expected result | Requirement scope |
| --- | --- | --- |
| Match two canonical SHA-256 dependencies across image and receipt | Metadata accepted | REQ-002 |
| Supply an empty dependency list | Leaf metadata accepted | REQ-002 |
| Supply matching empty, short, uppercase, or non-hex dependency text | `invalid_checksum` | REQ-002, REQ-012 |
| Put a malformed dependency after a canonical one | `invalid_checksum` | REQ-002, REQ-012 |
| Use different canonical dependency digests in image and receipt | `invalid_identity` | REQ-002, REQ-012 |
| Corrupt the receipt digest as well as dependency metadata | `receipt_invalid` retains precedence | REQ-002, REQ-012 |

For each scenario, prepare all ten required sections in member-name order and
compute the receipt digest through the production receipt encoder. For the
malformed-dependency cases, first assert that receipt validation succeeds;
then inspect the package-image validator's typed result. This distinguishes
dependency rejection from an unrelated broken fixture.

The production caller is `driver_source_pipeline_loading.spl` through
`runtime_std_load_baseline_v1`, `runtime_std_load_package_v1`, and
`package_image_validate_v1`. The provider metadata admission owner also calls
the validator. No new facade or caller is introduced.

These fixtures describe metadata and do not claim executable SMF, archive
mapping, exact closure membership, dependency uniqueness, or full provider
availability-error parity. Before acceptance, execute the focused spec on the
admitted self-hosted runner and regenerate this manual using SPipe docgen with
zero stubs.
