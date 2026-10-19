# Internal/external text foundation

Status: current-base source port; executable checks **UNRUN**. This is a dependency of the selected [UTF8/SOSIX plan](../03_plan/utf8_internal_sosix_plan.md), not whole-plan completion.

## Contracts and module boundaries

`std.common.encoding.external_text` supplies `Char = char`, `Text = text`, `AbstractChar.to_internal_char() -> Result<Char, CodecError>` and `AbstractText.to_internal_text() -> Result<Text, CodecError>`. Primitive and nominal external implementations use the same trait contracts. Classes use composition and traits; there is no inheritance or new grammar. The aliases do not change primitive physical storage.

`ExternalFormat` retains typed Encoding, TextByteOrder and BomPolicy. UTF-8 requires NotApplicable byte order; UTF-16 requires LittleEndian or BigEndian. Exact labels are utf-8, utf-16le and utf-16be; ambiguous/unknown labels fail before payload work. Preserve retains an initial U+FEFF as content, Require consumes/emits a signature, and Forbid rejects a matching signature. Byte order is never guessed.

`external_text` admits metadata and makes an owned byte copy. Conversion validates/transcodes strictly; malformed payload can exist in ExternalText until explicit conversion. `external_char` additionally requires exactly one scalar. ExternalText and ExternalChar expose public fallible copying `encoded_bytes`, non-copying `encoded_byte_length` and typed `external_format`. Private fields are not exposed through any new API. Character output uses the existing char-to-integer semantic cast and strict scalar encoder, not physical carrier reinterpretation.

`external_text_from_internal` and `external_char_from_internal` provide explicit output conversion, preserving embedded NUL. `external_validate_bom` admits only metadata and a matching required/forbidden prefix; successful admission says nothing about payload validity. Resource owners must call it at the appropriate actual stream position. This patch supplies no file/TCP resource adoption or ordinary SOSIX routing.

The foundation depends downward on the existing strict span codec `host_text_boundary_v1`, checked allocation/extraction in `common.text_bytes`, and scalar validation/encoding in `unicode_scalar`. Scalar adapters accept integer byte arrays of length one to four, reject non-byte values, malformed/overlong UTF-8, surrogates and out-of-range scalars, and never substitute replacement characters. The existing unicode_scalar_to_char and unicode_scalar_valid source remains byte-for-byte unchanged.

## Streaming and errors

ExternalTextDecoder owns format, carry, absolute consumed-byte offset, started/finished flags and the first error. Public mutable push/finish return typed Results; pending_byte_count exposes only a length. `_reject` and all fields remain private.

Push views the caller chunk with the previous carry through a non-copying span, resolves a starting BOM once, chooses complete scalar spans, validates/transcodes them, and retains at most three bytes. Offset/carry commit follows successful output and carry allocation. No entire-chunk concatenation or integer-byte widening occurs. A malformed incomplete scalar may be diagnosed on finish. First failure repeats unchanged; after successful finish later calls return StreamFinished. Independent decoders share no mutable state.

Errors preserve original external byte positions, including consumed signatures. Metadata errors use -1; truncation names the first missing byte; scalar cardinality errors use 0. The codec error mapping is typed. No process-global text mode, fallback encoding, replacement or normalization is introduced.

## Memory and provider boundaries

Checked packed allocations reject signed capacity overflow and allocation sentinels. Source uses preallocated packed copies and at most three bytes of carry. Whole UTF-8 validation directly materializes one Text; selected spans and UTF-16 use codec output then Text materialization. ExternalChar widens at most four decoded UTF-8 bytes after a length check. This is an algorithmic source bound, not measured allocation/RSS/throughput evidence.

The landed pure core_array/core_array_ops/core_array_query repair is a required source dependency. Its qualification remains FAIL_UNQUALIFIED after three retained attempts; no baseline/fixed runtime assertion ran. Hosted C packed support does not establish pure-owner safety. Actual packed byte8/128 tagged/raw ABI, provider identity, allocation failures, cleanup/refcounts, trait dispatch and privacy enforcement remain executable gates.

Final `bytes_to_text` materialization retains its inherited provider contract; end-to-end OOM handling is not established. See [the inherited provider allocation issue](../08_tracking/bug/abstract_external_text_inherited_byte_provider_allocation_2026-10-18.md). No cache is added without a measured repeated-encoding workload. Full host migration, physical Char layout/ABI and performance remain separate open requirements.

## Compatibility annotation and source provenance

The exact donor `impl AbstractText for text` signature retains explicit `self: text` and its HIR-RECEIVER-OWNER comment. The receiver-owner source repair has landed, but the historical object-producing compiler has not been newly qualified for an unannotated receiver. This annotation changes no language grammar and is scoped to that implementation; remove it only with executable evidence from the corrected producer. No compiler workaround or compiler source is imported here.

Foundation donor final SHA256: 9b4fcefb529b8a9e2be650d9ad0d06568becb99eecab87a0d1ffcb38784077a5, including BOM admission revision2. The only foundation source delta is explicit `pub` on the three ExternalChar accessors and decoder.pending_byte_count required by cross-module callers. The scalar prerequisite adds only the two existing pure integer codec functions and exports.

## Evidence and remaining requirements

The [selected requirements](../02_requirements/feature/abstract_external_text.md), [test plan](../03_plan/sys_test/abstract_external_text.md) and [authored scenario manual](../06_spec/03_system/lib/encoding/abstract_external_text_spec.md) map real assertions to each foundation behavior. Specs were authored before this production port. No source check, build, native test or bootstrap was invoked. Source-only review cannot mark UTF8-SOSIX-09/10 or the complete plan passed.
