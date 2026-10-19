# Typed text-session codec configuration

Status: source port; all executable cases **UNRUN**. This implements the configuration prerequisite of the selected [UTF8/SOSIX plan](../03_plan/utf8_internal_sosix_plan.md), not resource sessions or complete host migration.

## API and ownership

`std.nogc_sync_mut.io.text_session.TextSessionCodec` is a nominal class with eight private metadata fields and no mutating methods. `text_session_codec` selects input/output Encoding, ByteOrder and BomPolicy independently, followed by input/output byte limits, and returns `Result<TextSessionCodec, TextIoError>`. Unknown labels are never inferred as UTF-8.

The public readers are read_encoding/read_byte_order/read_bom, write_encoding/write_byte_order/write_bom, input_byte_limit/output_byte_limit. Each returns typed metadata; no public session signature returns ExternalFormat or an external text wrapper. Future resource owners construct their formats privately. `utf8_text_session_codec` explicitly selects UTF8/NotApplicable/Preserve both ways. The constant TEXT_SESSION_BYTE_LIMIT is 16777216 (16 MiB). Limits are inclusive 1..16777216. This configuration does not itself perform resource reads/writes or enforce their actual byte counts.

Public `validate` rejects limits before admitting either format. It delegates metadata admission to the existing external-text factory using empty payloads. Empty external values do not decode BOM content, so Require is accepted as metadata without requiring a stream prefix during construction. Both factories and validate retain the reviewed Result API and nested CodecError kind/offset. There is no new grammar, inheritance, generic transport, global mutable encoding or runtime ABI.

The config source is exact reviewed revision2 SHA256 6dd17e4b5d06f4cd40615303e21f675d879ea683cb69071cadd3f97462cbbe07. Previous review SESSION-CONFIG-001 removed format-returning accessors and made the actual scalar getters/validate explicitly public. The cross-module spec calls these same APIs. Private-field enforcement and native class allocation are still unqualified; "immutable" describes the source API, not an executed compiler privacy proof.

## Missing prerequisite supplied narrowly

`std.nogc_sync_mut.io.external_text_io` is copied from the existing donor as a pure error/conversion facade. TextIoError retains Io(text), Transport(IoError), Native(i64,text), Unsupported(text) and Codec(CodecError). The existing `std.io.types.IoError` is backed by common/io/types.spl, with kind/message/source constructor fields. The facade does not open/adopt/read/write/close resources, call foreign/runtime interfaces, access environment/process state, or import file/network owners.

The facade maps existing foundation results to nested Codec errors. io_external_bytes returns a defensive owned copy; io_external_from_internal/io_internal_text perform explicit strict conversions; io_legacy_utf8 is an explicitly named compatibility conversion returning textual diagnostics. io_text_error_message renders an existing error without replacing the typed result inside session config. No ordinary SOSIX API is routed through these helpers by this change.

## Requirements and authored evidence

| Selected-plan concern | Configuration/facade evidence | Still required |
|---|---|---|
| UTF8-SOSIX-02 metadata/endian/BOM | All scalar getters, asymmetric formats, explicit UTF8, unknown/incoherent diagnostics, Require metadata | Actual resource ingress/egress and BOM lifecycle |
| UTF8-SOSIX-03/05 strict errors/NUL | Facade strict malformed/unknown errors and UTF16LE BOM/NUL roundtrip | Admitted runtime and all host surfaces |
| UTF8-SOSIX-06/08 error distinctions/bounds | Nested typed errors, both limit endpoints and invalid sides, retained transport details | Provider errors, partial writes, counters and OOM on real resources |
| UTF8-SOSIX-09/10 memory/performance/qualification | Source bounds and authored actual API oracles only | Provider identity, executed tests, memory/latency/throughput and full qualification |

The original six real config cases are preserved, with four additional cases covering both limit endpoints, invalid limits on both sides, missing metadata negatives, and explicit validate under required BOM policy. Four facade cases exercise strict nested errors, owned byte copies, NUL/UTF16 roundtrip, malformed legacy/output conversion and existing error rendering. Specs were authored before the source port.

## Allocation and verification boundaries

Validation uses two empty external admissions, each retaining the packed allocator's minimum-capacity/allocation contract; selecting a 16 MiB limit does not allocate a 16 MiB payload. Repeated explicit validate calls repeat those bounded allocations. Future resource owners should admit once during construction and avoid this in hot I/O loops. No allocation-free or measured throughput/RSS claim is made.

The landed foundation, checked byte helpers, strict codec and pure packed-array source fix are required dependencies. Final text materialization and full cleanup/refcount/OOM behavior remain open inherited provider gates. Hosted C behavior does not qualify the pure provider, actual generated-byte tagging, trait dispatch or private class fields. This patch introduces no benchmark, fallback runner, bootstrap or compiler edit.

All execution remains UNRUN. The original three native failures remain counted in the root-owned user-authorized total of six; this port launches no attempt and does not reset that history. Root owns any separately gated next attempt. Source review cannot certify full-plan or Phase3 completion.
