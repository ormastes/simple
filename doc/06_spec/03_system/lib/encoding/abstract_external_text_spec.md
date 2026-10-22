# Working with internal and external text

Status: authored scenario manual, executable specification written but **not run**. This is not a generated PASS report. Canonical SPipe docgen and manual-quality verification remain required after an admitted runner is available.

Executable specification: `test/03_system/lib/encoding/abstract_external_text_spec.spl`.

## Read encoded text through the shared abstraction

1. Receive a UTF-16LE byte payload with explicit format metadata. The payload includes an ASCII letter, an embedded NUL and a supplementary character.
2. Construct ExternalText. This step validates metadata and owns the bytes; it does not claim the payload is well-formed yet.
3. Pass the external value to a generic AbstractText consumer and request internal text.
4. Observe the exact UTF-8 bytes, including NUL. The same consumer accepts an ordinary internal text value.
5. A primitive text value introduced through an unchecked raw provider is revalidated and malformed UTF-8 returns InvalidUtf8.

Covers REQ-001 and REQ-004. Expected UTF-8 bytes: `41 00 F0 9F 99 82`.

## Admit explicit metadata

1. Resolve exact protocol labels utf-8, utf-16le or utf-16be.
2. Keep byte order independent and typed: UTF-8 uses NotApplicable; UTF-16 needs an explicit order.
3. Reject an unknown label or an incoherent combination before inspecting even a malformed payload.
4. A bare utf-16 label is insufficient here; the protocol owner must supply resolved order.

Covers REQ-002. Metadata failures have byte_offset -1.

## Convert exactly one external character

1. Supply the two UTF-16BE surrogate units `D8 3D DE 42` as one ExternalChar.
2. Convert through AbstractChar and observe scalar semantics U+1F642 through the existing primitive semantic cast; this test does not establish its physical storage layout.
3. Reject empty payloads, multiple scalars and UTF-8 encodings of surrogate values.
4. A required initial signature is metadata; with Preserve it is an ordinary U+FEFF scalar. Thus preserved signature plus A contains two characters, while required signature plus A contains one.

Covers REQ-003. Physical layout and native casts are separately qualified by the char compiler lane.

## Write for an explicit destination

1. Convert internal UTF-8 containing A, NUL and U+1F642 to UTF-16LE with Require.
2. Observe exact output `FF FE 41 00 00 00 3D D8 42 DE`.
3. Decode using the same metadata and recover the original internal value.
4. Reject a required signature in the wrong declared byte order. Reject a forbidden matching signature on input or output.

Covers REQ-005. No endian guessing, replacement, normalization or process-global text mode is used.

## Keep ownership across a byte boundary

1. Construct ExternalText from a caller buffer.
2. Mutate that buffer and a separately returned encoded_bytes copy.
3. Observe that the external value still contains the original A.

Covers REQ-006. Raw binary APIs remain separate and their actual owner regressions are in the I/O lane.

## Decode transport chunks and finish

1. Feed a supplementary UTF-8 scalar over four chunks, then feed a UTF-16 surrogate pair over separate byte chunks.
2. Emit complete characters and assert pending_byte_count stays below four after every successful push.
3. Split required and forbidden BOMs across chunks and apply policy once at the beginning.
4. Finish a complete stream successfully. Finish incomplete UTF-8 or UTF-16 with TruncatedInput at the first missing absolute byte index.
5. After a malformed chunk, subsequent push/finish calls repeat the first error. After successful finish, further calls return StreamFinished.

Covers REQ-007. Output from earlier successful chunks remains owned by the caller. A failing chunk publishes no partial output. The complete-input codec is not itself an incremental decoder; this owner supplies bounded carry and terminal lifecycle.

<details>
<summary>Executable evidence and required qualification</summary>

- System specification: `test/03_system/lib/encoding/abstract_external_text_spec.spl`.
- Native generic contract fixture: `test/fixtures/native_abstract_external_text/main.spl`.
- Requirement map: `doc/02_requirements/feature/abstract_external_text.md`.
- Test plan: `doc/03_plan/sys_test/abstract_external_text.md`.
- Remaining evidence: admitted runner execution, primitive trait/HIR dispatch, physical Char semantic casts, cross-module privacy negative probe, branch coverage and required core/MCP smoke.

No passing evidence is asserted by this manual.

</details>

Revision2 also verifies every metadata field survives input/output, length inspection does not copy, UTF-16BE chunks are handled, and one failed decoder does not corrupt a second stream. Byte-copy accessors are fallible and the fixtures unwrap only expected successful copies. Packed-storage qualification is covered by a separate native provider fixture and remains unrun.

## Typed Result payload regression (2026-10-19)

The existing REQ-001/004/005 scenarios now retain explicitly typed `Result<Text, CodecError>` results from both AbstractText implementations. They assert exact UTF8 bytes for primitive text and UTF16LE/BE Require input, including NUL and a supplementary scalar, plus empty successes. Existing invalid UTF8, truncated UTF16, wrong-order required BOM and forbidden BOM cases now also pass through the generic AbstractText consumer and assert the same typed error kind/offset as direct calls. No scenarios were duplicated into another suite.

Historical donor compiler evidence (not a current-base execution): targeted attempt2 support/codec rows both report unresolved Infer(id=0,generation=0) in external_text.to_internal_text. That diagnostic does not identify the receiver/local. The source repair supplies exact declared payload types for the two implementations' Result bindings without changing calls or error propagation. The augmented scenarios and repaired compile are **UNRUN**; no object generation or runtime success is claimed.

## Current-base visibility and BOM admission

ExternalChar's three documented accessors and ExternalTextDecoder.pending_byte_count are explicitly public, matching the cross-module calls in this specification. Fields and the failure mutator remain private. The separate `test/01_unit/lib/encoding/bom_admission_spec.spl` checks metadata and the initial signature without claiming payload validity. Strict integer scalar boundary cases are in `test/01_unit/lib/common/encoding/unicode_scalar_codec_spec.spl`. These authored cases are UNRUN.
