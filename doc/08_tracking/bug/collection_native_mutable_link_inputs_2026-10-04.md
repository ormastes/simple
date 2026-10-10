# Collection receipt does not yet prove which object bytes the linker read

Status: source-confirmed correctness gap; runtime reproduction NOT RUN.

`collection_native_bind_capsule_v1` hashes an object after capsule admission.
`collection_native_publish_v1` hashes the same path after linking. The linker
receives shared mutable paths through `object_files`. A replacement between
admission and binding can associate unadmitted bytes with the capsule. An
A-to-B-to-A replacement during linking can also pass both digest checks while
the executable contains B. The final executable digest identifies output bytes;
it cannot establish the claimed relationship to the admitted MIR by itself.

Required repair: obtain immutable, owned link inputs while their object receipt
is admitted, and pass exactly those retained inputs to the linker. Keep their
identity alive through output publication. A post-link hash alone cannot close
this gap. `driver_cold_hir_persist_verified_objects_v1` and
`cold_hir_native_objects_persist_v1` provide existing CAS persistence to examine,
but persistence is currently conditional and does not replace linker inputs.

Required executable cases: replace a shared source object after admission;
replace it during link and restore the original before publication; attempt
replacement of the retained input; prove either rejection or consumption of
the originally admitted bytes. Exercise cold, object-cache, and no-op delivery
paths. Tests must use the actual linker/publication boundary.

Some generated modules also have empty `source_identity` when no unique source
path is available. Current receipts do not prove complete source provenance.
Until these gaps and runtime validation are closed, the sidecar is diagnostic
evidence only and cannot satisfy profile-to-native semantic acceptance or justify
pushing the compiler implementation as stable.


## Retained linker inputs implemented (2026-10-10)

Binding now checks the object bytes against the existing admitted capsule
receipt instead of accepting a newly observed digest. Each requested collection
build copies those bytes into a fresh private directory, verifies their digest,
and passes the retained paths to every standalone linker mode. Cache metadata
keeps its original paths. Publication checks the retained inputs and cleans them
up afterward. Source cache replacement cannot change the retained bytes.

The focused spec now covers a mismatched admitted digest, source replacement
and restoration after retention, and rejection of a replaced retained input.
These Simple cases and actual linker/publication fault injection are NOT RUN;
this remains an unqualified implementation, not a native acceptance PASS.
Path-based linking assumes private build-owned paths are not modified by a
hostile same-user process during linking; no descriptor-pinning guarantee is
claimed. Grouped receipt support and complete source provenance remain open.
