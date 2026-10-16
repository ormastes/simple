# A174 aggregate receiver provenance failures (2026-10-16)

Status: pending bug database admission; source workaround candidate, native UNEXECUTED.

The immutable pure-Simple Windows producer SHA256 a174b8e70b0a0ea4531db2ac5b8553f216590a7fbad0567cd9e40fd8e4630994 compiled the 231-module provisional authority closure with LLVM23.1.3/MSVC. Final authority attempt3 reached MIR semantic failures, exit1, with zero objects. This report groups a subset of those failures; it does not establish one compiler root cause.

Retained external evidence: `C:/dev/simple-bootstrap-storage/phase3-validation-20261016/authority-attempt3-failure-table.md`, terminal report and full-phase3-authority-error-membership.json. Original source snapshot SHA256 dde909cbacab0ed2caf790a525668761d1eb8cd7af0a2a65bd4e7f893b4757b5. Candidate base58993f7476f0bee702e61bb19c7b46e92b57271a.

Observed diagnostics (original source lines):

- interface_action_archive.spl284/285/331 unresolved contains;288/295/349 for-in collection MIR type I64 despite declared array fields.
- scv/integrity.spl486 for-in table.rows collection MIR type I64; SdnTable.rows is declared [SdnRow].
- database/core.spl655/658 unresolved row.get; preceding typed_table:SdnTable already exists.
- scv/compile_snapshot.spl275 unresolved split; rows comes from a conditional with a bare empty-array branch.
- gzip/inflate.spl218 for-in collection MIR type I64; helper lengths parameter lacks its numeric-array annotation.
- package_archive_cache.spl381 unsupported Result unwrap payload type; payload producer explicitly returns Result<(text,text,text,text),text>.

Temporary workaround: bind read-only projected arrays and row elements to existing concrete types before contains/iteration/get; explicitly type snapshot rows/fields; match tuple Result Ok/Err while retaining exact original Err text and semantic payload admission. Owner mutations remain on original owners after complete validation, and staged transaction commit/closed behavior is preserved. The Huffman helper parameter and numeric-array builder annotations are an ordinary missing-signature/type-clarity repair, distinct from already-declared receiver workarounds.

Recovery: remove temporary receiver aliases after a rebuilt producer demonstrates correct projected array/element and tuple Result lowering on the same positive/negative cases. No recovery commit is currently claimed. Canonical @workaround tags use this report ID and an explicit recovery condition.

No validation branches, stream bounds, error messages, or modules are removed. package_archive_cache.spl415 concat remains unchanged: receiver and dependency field are already [text], and actual intrinsic support needs separate investigation. Generated-code nil predicates and enum metadata failures are separate lanes.

Qualification: source diff review only. No compiler invocation or runtime test has been performed for this candidate; authority budget is exhausted (3/3), with no fourth retry. Future qualification must check transaction atomic failures, malformed database rows/inventory/Huffman streams and exact archive Err propagation, plus successful actual values. Static annotations alone are not evidence A174 accepts the candidate or that the full Phase3 build passes.
