# Native enum projection qualification

Status: **scoped combined-producer PASS; standalone release-head qualification pending**.

Indexed records previously lost declared element type/layout metadata, and enum fields carried a bare owner while provider methods used canonical owner keys. The three source changes preserve declared element HIR types, preserve canonical enum-field owners without changing their HIR rebinding keys, and record registered qualified Struct layouts after indexing. Primitive decoding, array storage classification, privacy, and ambiguity checks retain their existing behavior.

## Exact qualified lineage

- Combined compiler source: `cceddeb91c43645e5f70f5cc76ad61daa02562b3`.
- Pure-Simple producer: `/home/yoon/dev/simple-bootstrap-next-20261011/build/native_probe/hir-cache-owned-miss/simple`.
- Producer SHA-256: `44a540d538241e202e2dc00440591c4fd9567474706c310f3c75367638325134`.
- Release draft base: `f182a1d977d333285c481ea86278aa6420375a46` (`release/1.0`, freshly fetched; newer than the initially requested `74a3eebe819`). The target helper bodies lacked all three changes. No duplicate source hunks were introduced.
- Source origins: `cd7c37d215c`, `3a19f9b833a`, and `8f24501fd13`.

The qualified producer contains additional integrated fixes beyond this release draft. The two edited source sections and all four qualified fixture files match the frozen source exactly, but this is not a standalone build or execution qualification of the PR head. Earlier failed attempts remain documented; no green fixture was repeated.

## Real native gates

| Fixture entry | AArch64 ELF / execution | LLVM 18 RISC-V object |
|---|---|---|
| `nested_enum_field_owner/indexed_layout.spl` | EM183, exit 0, `INDEXED_STRUCT_LAYOUT_PASS` | EM243, build exit 0 |
| `nested_enum_field_owner/main.spl` | EM183, exit 0, `NESTED_ENUM_FIELD_OWNER_PASS` | EM243, build exit 0 |

The first fixture checks nested arrays returned from a function, a typed nested-array parameter, two enum variants, and an enum field following an integer marker. The original three-file collision fixture is unchanged from its failing producer-19f receipt; it checks both foreign providers with identical enum/variant/method names, exact distinct results, and nested field/index receivers.

Builds used explicit source roots and entry closures, CPU 1, one compiler worker, 120-second limits, LLVM 18, and no Rust compilation or stub fallback. ARM programs ran under 20-second limits. Separate producer/entry/target cache directories isolated HIR and frontend/object caches. RISC-V builds began only after both ARM execution oracles passed. The RISC-V objects were not executed.

[Machine-readable receipt](../evidence/native_enum_projection_2026-10-11.json) records exact commands, fixture and artifact hashes, timings, exit codes, architecture identities, and ARM output. Local logs and artifacts remain under `/home/yoon/dev/simple-enum-field-owner-20261011/build/native_probe/enum-field-owner/stable-keys/44a540d538241e202e2dc00440591c4fd9567474706c310f3c75367638325134/`.

## Pending gates

This draft does not claim full compiler/lib/MCP checks, MCP native smoke, the SSpec suite, canonical admission, or standalone release-head qualification. The original real `flight_rule_indexed_owner.spl` registry fixture and a full runner were not rerun in this cycle. These remain pending before merge/release. No compiler reconstruction, full-runner retry, target emulation, or release publication occurred in this lane.
