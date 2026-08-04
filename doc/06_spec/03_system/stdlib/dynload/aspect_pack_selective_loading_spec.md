# SFM Aspect-Pack Selective Loading

> Executable source: `test/03_system/stdlib/dynload/aspect_pack_selective_loading_spec.spl`

| Tests | Active | Skipped | Pending |
|---:|---:|---:|---:|
| 6 | 6 | 0 | 0 |

## Purpose and audience

This manual is for SFM codec, loader, security, and release reviewers. It
provides executable evidence for REQ-AF-005 and the pack-validation portion of
REQ-AF-007.

## Preconditions

- Use a current pure-Simple full CLI with `SIMPLE_LIB=src`.
- Do not use the Rust seed or codegen stub fallback.
- Ordinary SMF payload bytes remain opaque to the SFM2 codec.

## Operator workflow

1. Build one bounded SFM2 fixture with two independently framed SMFs.
2. **Load only the selected SMF module closure.**
3. Corrupt only the unselected frame and confirm selection remains valid.
4. **Reject an invalid aspect pack** before publication.

## Scenarios

- **should expose the selected ordinary SMF bytes without decoding another
  frame** — corruption in the unselected frame does not affect selected bytes.
- **should preserve manifest and independent compression metadata** — checks
  pack identity, entry count, and per-frame modes/sizes.
- **should report an absent module without exposing another payload** — requires
  `E-APACK003`.
- **should reject unsupported SFM version and kind before publication** —
  validates the explicit SFM2 kind/version contract.
- **should reject corruption when the affected frame is selected** — validates
  selected stored-content integrity.
- **should reject trailing bytes even when the directory is otherwise valid** —
  rejects noncanonical aliases/extensions.

## Pass/fail criteria

PASS requires all six scenarios, concrete byte/metadata/error assertions, no
placeholder passes, and no access to an unrelated payload on selection. A
crash, seed execution, unchecked trailing data, or partial acceptance is FAIL.

## Evidence and provenance

- Requirements: `doc/02_requirements/feature/aspect_facet_dynload_smf_pack.md`
- Test plan: `doc/03_plan/sys_test/aspect_facet_dynload_smf_pack.md`
- Design: `doc/05_design/language/aop/aspect_facet_dynload_smf_pack_design_2026-08-04.md`
- Executable source SHA-256:
  `7b7657e93ce249cefb723ba454ceb95a41fa89303321ec8081d49da5320be0d6`

<details>
<summary>Executable SSpec</summary>

The sibling executable source is authoritative for `build_aspect_pack_fixture`
and every mutation/assertion.

</details>

## Compatibility and limitations

The stored-content hash is a deterministic corruption guard. Exact pack/module
SHA-256 validation belongs to `AspectPackProvider` and is exercised by the
catalog/provider evidence. Authentication/signature policy is distinct from
both mechanisms.
