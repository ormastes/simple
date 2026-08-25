<!-- codex-design -->
# SPipe Knowledge Compiler — Cooperative Streaming Provider Detail Design

**Status:** Implementation-ready focused design
**Date:** 2026-08-25
**Parent design:** `spipe_knowledge_compiler.md`
**Architecture:** `../../../04_architecture/infra/spipe/spipe_knowledge_compiler_cooperative_streaming.md`
**Requirements:** REQ-SPKC-013–015; NFR-SPKC-001–004, 011–016, 019, 021–022, 025

## 1. Scope and current migration seam

This design replaces false whole-call deadline polling with a byte-preserving,
bounded reactor and resumable work. It does not change protocol 1.0's logical
wire frame, lexical semantics, fixed-point score contract, lifecycle receipt
authority, candidate roots, or JavaScript/Simple parity obligations.

The current source maps to the target as follows:

| Current owner | Current behavior | Target owner |
|---|---|---|
| `main.spl` | blocking whole-frame `read_exact`, bytes-to-text, whole response write | `ProviderSessionOwnerV1` + `ProviderByteStreamPort` + frame decoder/encoder |
| `protocol.spl` | length-prefix helpers over `text` | protocol constants plus byte-only frame state |
| `wire_dispatch.spl` | whole-tree JSON parse and synchronous dispatch | iterative typed envelope decoder plus work-machine factory |
| `wire_json.spl` | recursive canonical JSON and joined text | iterative canonical decoder/emitter over segmented bytes |
| `query_clock.spl` | clock plus synthetic cancellation predicate | monotonic clock inside request control/checkpoint composition |
| `service_deadline.spl` | checkpoints around service calls | request-local machines with checkpoints inside every bounded stage |
| `lexical.spl` | loop polling around batch analysis and string assembly | cached streaming analysis plus resumable score/explain/emission machines |
| `sha256.spl` callers | one-shot payload/lifecycle hashes | incremental SHA state with one-shot compatibility facade |
| `wire_query.spl` stats | `platform_name()==linux` and direct peak-RSS call | `ProviderProcessStatsPort` capability/sample contract |

`cancel:false` is the only valid current production claim. Source-only clocks
or synthetic cancellation oracles do not authorize `cancel:true`.

## 2. Exact common vocabulary

The following names and semantics are frozen for this slice. New optional
fields require a compatible minor contract; changing a status or ownership rule
requires an architecture revision. Focused-architecture Section 4.1 is the
normative signature authority; the code blocks below reproduce and elaborate
that contract without introducing aliases.

Closed text enums are:

```text
ProviderByteIoStatusV1 = data | timeout | eof | error
ProviderFrameStateV1 = header | payload | complete | failed
ProviderDecodeStateV1 = need_input | progressed | complete | failed
ProviderRequestStateV1 = registered | running | cancel_requested |
                         commit_admitted | completed
ProviderWorkStepKindV1 = continue | ready | failed
ProviderCancelDispositionV1 = cancelled | already_complete | target_not_found
ProviderCommitKindV1 = none | index_apply | index_publish | lifecycle_control
```

Unknown enum values fail closed. They are never mapped to a default success.

### 2.1 Raw byte stream

```simple
struct ProviderByteReadV1:
    status: text
    bytes: [u8]
    detail: text

struct ProviderByteWriteV1:
    status: text
    written_bytes: i64
    detail: text

trait ProviderByteStreamPort:
    me read_some(maximum_bytes: i64,
                 deadline_at_ms: i64) -> ProviderByteReadV1
    me write_some(bytes: [u8], offset: i64, maximum_bytes: i64,
                  deadline_at_ms: i64) -> ProviderByteWriteV1
```

`read_some(data)` owns and moves 1..`maximum_bytes` bytes to the session.
`write_some(data)` reports 1..the requested remaining bytes and borrows the
input only for the call. Short positive progress is valid. Zero progress is
never `data`: EAGAIN/would-block maps to `timeout` with `detail=would_block`, an
elapsed timer maps to `timeout` with `detail=deadline`, closed peer maps to
`eof`, and other host failure maps to `error`. A malformed adapter result closes
the transport as `internal_error`; the session never busy-retries it.

The port is implemented by the existing `app.io`/host boundary. Provider app
code may not import runtime externs, `/proc`, Windows APIs, or platform names.
The current blocking inherited-stdio calls and nonblocking piped-child helpers
do not satisfy this contract. A prerequisite runtime-owner lane must add a
binary-safe pollable inherited-stdio primitive with partial progress, distinct
would-block/deadline/EOF/error outcomes, and absolute monotonic deadlines; a
concrete `app.io` adapter then binds it. Capability records and normalization
without that adapter are useful but explicitly partial.

### 2.2 Frame decoder and encoder

```simple
struct ProviderFrameCompletionV1:
    payload_bytes: i64
    first_header_at_ms: i64
    completed_at_ms: i64

struct ProviderFramePayloadChunkV1:
    bytes: [u8]
    offset: i64
    count: i64
    frame_payload_offset: i64

struct ProviderFrameDecodeEventV1:
    kind: text                 # none | header | payload
    declared_payload_bytes: i64?
    payload: ProviderFramePayloadChunkV1?

struct ProviderFrameDecodeStepV1:
    consumed_bytes: i64
    state: text
    event: ProviderFrameDecodeEventV1
    error_code: text

class ProviderFrameDecoderV1:
    # private: header bytes/cursor, declared length, payload segments/count,
    # first-header/completion timestamps, limits, state
    static fn configured(limits: ProviderTransportLimitsV1) \
        -> Result<ProviderFrameDecoderV1, text>
    me push(bytes: [u8], offset: i64, observed_at_ms: i64) \
        -> ProviderFrameDecodeStepV1
    me take_complete() -> Result<ProviderFrameCompletionV1, text>

struct ProviderSegmentedBytesV1:
    segments: [[u8]]
    total_bytes: i64

struct ProviderFrameWriteLoanV1:
    bytes: [u8]
    offset: i64
    remaining_bytes: i64

class ProviderFrameEncoderV1:
    static fn configured(payload: ProviderSegmentedBytesV1,
                         limits: ProviderTransportLimitsV1) \
        -> Result<ProviderFrameEncoderV1, text>
    fn complete() -> bool
    fn next_write(maximum_bytes: i64) -> ProviderFrameWriteLoanV1
    me advance(written_bytes: i64) -> Result<(), text>
```

The decoder validates exactly eight lowercase hexadecimal header bytes,
checked length arithmetic, and `max_frame_bytes`. It records the first header
timestamp when the first header byte is accepted. `push` reports exactly how
many input bytes it consumed and emits at most one event. It stops immediately
after byte eight to emit one `header` event, even when the caller's input also
contains payload; the caller resumes at `offset + consumed_bytes`. Subsequent
calls emit nonempty `payload` events in increasing `frame_payload_offset`
order. Each event's count is bounded by `read_chunk_bytes` and remaining
declared payload bytes. `declared_payload_bytes` is `nil` only for `none`
before a complete header and is exact for `header`/`payload`; `payload` is
non-`nil` only for the `payload` kind.

`ProviderFramePayloadChunkV1` is a fresh bounded owner-created result moved to
the caller. Only the decoder owns and advances the framing cursor, and it keeps
no alias to an emitted chunk. The session moves each chunk synchronously into
the iterative UTF-8/JSON/SHA pipeline. No session, parser, or envelope layer
keeps a second frame-payload cursor or concatenated frame copy. `take_complete`
is legal only after the declared payload has been emitted and consumed; it
returns final byte/timestamp metadata, contains no payload bytes or segments,
and resets decoder state. Thus decoder memory is bounded by the eight-byte
header and one result chunk rather than `max_frame_bytes`.

The frame encoder prepends the exact eight-byte lowercase hexadecimal length
without converting payload bytes to text. It traverses header then payload
segments with one cursor. Protocol 1.0 remains byte-identical.

### 2.3 Transport and request limits

```simple
struct ProviderTransportLimitsV1:
    max_frame_bytes: i64
    read_chunk_bytes: i64
    write_chunk_bytes: i64
    max_queued_requests: i64
    max_pending_bytes: i64
    ingress_timeout_ms: i64
    output_timeout_ms: i64

struct ProviderJsonLimitsV1:
    max_depth: i64
    max_tokens: i64
    max_aggregate_members: i64
    max_decoded_string_bytes: i64
    max_total_decoded_bytes: i64

struct ProviderAnalyzerLimitsV1:
    max_input_bytes: i64
    max_scalars: i64
    max_normalization_segment_code_points: i64
    max_case_context_code_points: i64
    max_token_bytes: i64
    max_tokens: i64

struct ProviderStepLimitsV1:
    max_bytes: i64
    max_json_events: i64
    max_unicode_scalars: i64
    max_sha_blocks: i64
    max_comparisons: i64
    max_output_bytes: i64
```

Protocol 1.0 freezes `max_frame_bytes=1_048_576`,
`min_deadline_ms=1`, and `max_deadline_ms=30_000`. The initial qualification
profile uses 16 KiB read/write chunks, exactly 16 queued ordinary requests in
addition to one active request, cumulative pending bytes 2 MiB, JSON depth 16,
262,144 lexical JSON tokens, 65,536 aggregate members, 1 MiB decoded bytes,
normalization and case-context carry 1,024 code points each, and per-step
ceilings of 4 KiB, 256 JSON events, 1,024 scalars, 64 SHA blocks, 256
comparisons, and 4 KiB emitted bytes. Each complete object name/value pair and
each complete array element consumes one aggregate-member unit. These maxima
are frozen for this slice; hosts may configure stricter values but may not
silently widen them.

The queue, pending-byte, transport-timeout, step, and checkpoint-gap values are
host-local configuration and payload-free qualification evidence. Protocol 1.0
has a closed initialization schema, so this design adds none of them to the
handshake. A future wire-visible limit record requires an explicit compatible
protocol minor and new closed-schema vectors.

## 3. Iterative canonical JSON pipeline

### 3.1 States and interfaces

```simple
struct ProviderJsonEventV1:
    kind: text
    key: text?
    text_value: text?
    integer_value: i64?
    boolean_value: bool?
    byte_start: i64
    byte_end: i64

struct ProviderDecodeStateV1:
    kind: text
    consumed_bytes: i64
    event_pending: bool

struct ProviderCanonicalJsonResultV1:
    payload_sha256: text
    raw_bytes: i64
    token_count: i64
    aggregate_members: i64
    maximum_depth: i64

class ProviderUtf8DecoderV1:
    static fn configured() -> ProviderUtf8DecoderV1
    me push(bytes: [u8], offset: i64, count: i64, final_chunk: bool,
            budget: ProviderBudgetPort,
            checkpoint: ProviderCheckpointPort) \
        -> Result<[i64], text>

class ProviderCanonicalJsonDecoderV1:
    static fn configured(limits: ProviderJsonLimitsV1,
                         sha: Sha256StreamV1) \
        -> ProviderCanonicalJsonDecoderV1
    me push(bytes: [u8], offset: i64, count: i64, final_chunk: bool,
            budget: ProviderBudgetPort,
            checkpoint: ProviderCheckpointPort) \
        -> Result<ProviderDecodeStateV1, text>
    me next_event() -> Result<ProviderJsonEventV1?, text>
    me finish() -> Result<ProviderCanonicalJsonResultV1, text>

class ProviderEnvelopeDecoderV1:
    static fn configured(host: ProviderHostBindingV1,
                         limits: ProviderLimitContractV1) \
        -> ProviderEnvelopeDecoderV1
    me accept(event: ProviderJsonEventV1,
              checkpoint: ProviderCheckpointPort) -> Result<(), text>
    me finish(frame: ProviderFrameCompletionV1,
              payload_hash: text) -> Result<ProviderTypedEnvelopeV1, text>
```

`ProviderCanonicalJsonDecoderV1` has an explicit lexical cursor and an explicit
stack of `JsonContainerFrameV1`; it never calls itself recursively. A container
frame stores object/array kind, expected next token, item count, last canonical
key bytes, and schema cursor. It rejects:

- malformed or overlong UTF-8, surrogate encodings, and incomplete sequences;
- whitespace outside strings;
- noncanonical escapes or integer lexemes, fractions/exponents, or values
  outside signed safe-integer range;
- duplicate or non-increasing object keys;
- extra/missing keys, excess depth/tokens/members/elements/decoded bytes;
- bytes after the single root value or before the declared frame end.

`push` consumes only a prefix of `[offset, offset + count)` and reports that
prefix in `consumed_bytes`; it emits at most one event. The closed state kinds
are `need_input`, `progressed`, `event`, and `complete`. When the result is
`event`, the decoder owns exactly one pending event. `next_event` moves and
clears it. Until that move, `push` returns `consumed_bytes = 0` without touching
the raw cursor, SHA, UTF-8 carry, budget, or checkpoint. A caller resubmits the
unconsumed suffix; `final_chunk` applies only after the whole offered final
slice has been consumed.

A completed primitive adjacent to `]` or `}` is an explicit two-step boundary:
the first `push` prefix ends with the primitive event, and after that event is
moved the resubmitted suffix produces the closing-container event. The decoder
must not consume the closer speculatively, queue both events, report
`event_queue_full`, or emit either event twice. Likewise, container grammar
rejects `[1,]` and `{"a":1,}`. Key-order state represents absence separately
from key bytes, so `{"":1,"":2}` is a duplicate-key error rather than two
unconditionally admitted empty keys.

The event-kind set is closed to `start_object`, `end_object`, `start_array`,
`end_array`, `key`, `string`, `integer`, `boolean`, and `null`. Spans are exact
half-open canonical-payload offsets `[byte_start, byte_end)`: container spans
cover their one punctuation byte, and key/string spans include their opening
and closing quotes. Field validity is closed: `key` is present only for a
`key` event; `text_value` is present only for `string`;
`integer_value` only for `integer`; and `boolean_value` only for `boolean`.
Every non-applicable field is `nil`; empty string, zero, and `false` remain
valid values and are never field-absence sentinels.

Depth is the number of simultaneously open object/array containers. A root
container has depth one, nested containers increment it, and any primitive root
has depth zero. One object member is charged only when its complete value
finishes; one array member is charged only when its complete element finishes.
Opening/closing a container does not add another member, and the root is not a
member. The JSON decoder accepts exactly one root of any closed JSON kind,
including a primitive. The envelope builder alone rejects a non-object root as
an invalid protocol schema after canonical decoding.

String acceptance uses only pinned UCD 17.0.0 NFC data. The decoded scalar
sequence must already be NFC; the decoder rejects rather than silently rewrites
it, and host Unicode tables are not consulted. Keys compare in strict unsigned
UTF-8 byte order after that NFC check; equality is a duplicate. The canonical
escape table is exact: quotation mark `\"`, reverse solidus `\\`, U+0008
`\b`, U+0009 `\t`, U+000A `\n`, U+000C `\f`, and U+000D `\r`. Other
U+0000–U+001F controls use lowercase `\u00xx`. All remaining scalars are raw
shortest-form UTF-8; `\/`, uppercase hex, unnecessary `\u` escapes, and
surrogate escapes are rejected.

The decoder owns one raw-byte cursor and one `Sha256StreamV1`. It hashes exactly
the consumed canonical prefix once and never hashes reconstructed text or
maintains a parallel canonical cursor. `finish` is legal only after final input,
a complete single root, an empty stack, and no pending event. It returns exactly
`payload_sha256`, `raw_bytes`, `token_count`, `aggregate_members`, and
`maximum_depth`. Successful finish latches `decoder_complete`; any failure
latches its first exact reason. All later `push`, `next_event`, and `finish`
calls return that terminal reason and cannot consume bytes, emit events, or
publish a digest.

Typed operation builders consume events and hold only bounded fields. They do
not retain a generic `any` graph. Object schemas provide canonical field order,
required/optional fields by negotiated minor, and operation-specific limits.
The payload SHA is updated over the exact validated raw bytes, not reconstructed
text.

### 3.2 Error boundary

Invalid header, `frame_too_large`, `invalid_utf8`, incomplete EOF, or
`noncanonical_json` before a complete typed and host-bound envelope are
transport-local fatal errors: discard decoder state and close silently. A
request ID or operation recovered from a partially invalid payload is not safe
to reflect. After `ProviderEnvelopeDecoderV1.finish` succeeds, closed-schema,
limit, deadline, cancellation, and operation errors use the normal bound wire
error. This separation is mandatory in fixtures and logging.

`frame_too_large` and `invalid_utf8` are the closed, payload-free local
`TransportDiagnosticV1` classes. They are not members of `ProviderErrorV1` and
cannot create a `ProviderResponseV1` before binding.

### 3.3 Canonical emission

```simple
trait ProviderByteSinkPort:
    me append(bytes: [u8], offset: i64, count: i64,
              budget: ProviderBudgetPort) -> Result<(), text>
    fn total_bytes() -> i64

class ProviderSegmentedByteSinkV1 with ProviderByteSinkPort:
    static fn configured(segment_bytes: i64,
                         maximum_bytes: i64) \
        -> Result<ProviderSegmentedByteSinkV1, text>
    me take() -> ProviderSegmentedBytesV1

class ProviderCanonicalJsonEmitterV1:
    static fn configured(plan: ProviderResponsePlanV1,
                         maximum_output_bytes: i64) \
        -> Result<ProviderCanonicalJsonEmitterV1, text>
    me step(limits: ProviderStepLimitsV1,
            sink: ProviderByteSinkPort,
            sha: Sha256StreamV1,
            budget: ProviderBudgetPort,
            checkpoint: ProviderCheckpointPort) \
        -> ProviderEmitterStepV1
    me take_ready() -> Result<ProviderEmittedResponseV1, text>
```

Response schemas supply fields in canonical byte order through the flat plan;
the emitter uses one tape cursor plus a bounded string-escape subcursor. A plan
contains at most 262,144 instructions. One call consumes at most 256
instructions and emits at most 4,096 bytes, or stricter positive configured
limits. It updates SHA from the same emitted slice. It never forms `parts`,
calls `join`, recurses, maintains a JSON value stack, or serializes into a
second full string. `ProviderEmitterStepV1.kind` is closed to
`continue | ready | failed`; only `failed` carries the latched closed reason.
`ProviderSegmentedBytesV1` has one target
canonical owner in `segmented_bytes.spl`; the accepted sink imports it. The
unaccepted `frame_encoder.spl` still declares a parallel type, so migrating the
encoder to that owner is a red/future obligation and current imports do not
prove the target ownership contract. The sink requires positive configured
limits. Each append validates its checked range and prospective total, then
charges logical output bytes and the exact newly required segment allocation
through one `budget.charge_all` batch, all before mutation or allocation. The
batch aggregates duplicate categories with checked arithmetic and validates
all category limits before committing any counter, so a second-category
failure leaves output-byte and allocation counters unchanged. Segments stay bounded.
The emitter, not an arbitrary caller, may move the sink through `take_ready`,
and only after it reaches `ready`; no alias remains. The segmented sink is
necessary because the protocol prefix requires payload length before output.

## 4. Incremental SHA-256 contract

```simple
class Sha256StreamV1:
    # private: eight state words, 64-byte partial block, one fixed reusable
    # owner-local 64-word message schedule, partial length, checked total
    # length, finalized flag
    static fn begin(domain: [u8]) -> Result<Sha256StreamV1, text>
    me update(bytes: [u8], offset: i64, count: i64,
              budget: ProviderBudgetPort,
              checkpoint: ProviderCheckpointPort) -> Result<(), text>
    me finish(budget: ProviderBudgetPort,
              checkpoint: ProviderCheckpointPort) -> Result<text, text>
```

The state processes complete 64-byte blocks incrementally and retains at most
one partial block plus one fixed 64-word schedule workspace. The workspace is
owner-local O(1) state: it is never passed or returned and is not reallocated
per compression block. This removes repeated schedule allocation but does not
claim zero-copy processing. `finish` applies SHA padding and the checked bit length
without materializing `domain + payload + padding`. Calling update/finish after
finalization or overflowing the declared byte budget fails closed.

`begin` accepts only the fixed provider domain separator and rejects domains
longer than 63 raw bytes as `invalid_hash_domain`. This keeps construction
compression-free: every compression, including padding blocks, is charged as
one `hash_blocks` unit immediately before execution and is followed by a
request-scoped checkpoint. All protocol-defined provider domains are below the
bound.

Every domain-separated provider hash feeds exact domain bytes and length
bindings before content. The existing one-shot functions remain compatibility
facades and, after parity, may internally instantiate `Sha256StreamV1`; the
provider hot path must never fall back from streaming to one-shot based on
input size.

Required parity covers lengths 0, 1, 55, 56, 63, 64, 65, 4,095, 4,096,
4,097, and 1,048,576. Lengths through 65 exercise every single split. The
4,095/4,096/4,097/1-MiB cases exercise exact block/quantum/end boundaries plus
multiple deterministic fixed-seed irregular partitions that cross SHA block
boundaries; they do not enumerate every possible split. Frozen
receipt/replay/candidate/payload and domain-input preimages must be streamed
from their authoritative exported builders, not reconstructed by the test or
validated only through a one-shot output comparison. Every partition retains
exact digest and canonical-byte parity.
`update` also proves
fail-closed range validation for negative offset, negative count, and
`offset > bytes.len`; no rejected range may read, hash, or advance
buffered/compressed digest content.
Charge failure occurs before its compression. Checkpoint failure after a
compression terminalizes the stream and prevents digest publication; it does
not promise rollback of already-compressed internal state. The digest and canonical emitted bytes must match together
in an executed post-fix run. Static inspection or a source correction without
that PASS is not gate evidence.

## 5. Streaming Unicode analyzer

### 5.1 Pipeline and ports

```simple
struct ProviderAnalyzedTokenV1:
    value: text
    position: i64
    exact_identifier: bool

trait ProviderAnalyzedTokenSinkPort:
    me emit(token: ProviderAnalyzedTokenV1) -> Result<(), text>

class ProviderStreamingAnalyzerV1:
    # private: UTF-8 carry; first NFC segment; lowercase context/pending sigma;
    # second NFC segment; token bytes/position; identifier trim state
    static fn configured(identity: AnalyzerIdentity,
                         limits: ProviderAnalyzerLimitsV1,
                         identifier_field: bool) \
        -> Result<ProviderStreamingAnalyzerV1, text>
    me push(bytes: [u8], offset: i64, count: i64, final_chunk: bool,
            sink: ProviderAnalyzedTokenSinkPort,
            budget: ProviderBudgetPort,
            checkpoint: ProviderCheckpointPort) \
        -> Result<ProviderDecodeStateV1, text>
```

The semantic pipeline is exactly the existing UCD-17 contract:

```text
NFC(input) -> Unicode default lowercase -> NFC -> token classification
```

The first NFC state recursively decomposes each scalar, insertion-orders only
the current canonical-combining segment, composes it, and flushes it when the
next starter closes the segment. Hangul decomposition/composition uses the same
generated tables/algorithm as batch normalization.

Default lowercase maps the flushed normalized scalars. It tracks whether the
previous non-case-ignorable scalar is cased. A sigma with cased context is held
with following case-ignorable scalars until the next non-case-ignorable scalar
or EOF decides Final_Sigma. Mapping expansion is fed through the second NFC
state. The explicit `max_case_context_code_points` bound prevents an unbounded
case-ignorable run.

The tokenizer classifies the second-NFC scalars with the same UCD-17
alphabetic/decimal/mark/underscore tables, buffers only the current bounded
token, increments logical positions before stop-word removal, and emits at a
delimiter or EOF. Identifier fields also emit the exact NFC/lowercase/NFC
trimmed identifier at position zero; leading/trailing whitespace is handled by
a bounded trim cursor, not by retaining a second whole normalized field.

Inputs exceeding combining, case-context, scalar, token, or output-expansion
limits return `limit_exceeded`; they never split a combining sequence, guess
Final_Sigma, truncate a token, or claim parity. Analyzer cache identity contains
Unicode version, generator digest, normalization/lowercase/tokenizer semantics,
limits version, stop-word hash, and field schema.

### 5.2 Cache and invalidation

`AnalyzedFieldCacheKeyV1` is `(scope_digest, content_hash, field_name,
field_weight_milli, analyzer_identity_hash, analyzer_limits_hash)`. Cached
values contain immutable positioned tokens, exact token when applicable,
length, and term frequencies. A document/content/field change invalidates that
entry and derived postings/corpus aggregates. Analyzer identity/table/limit
change invalidates the complete lexical segment. Transport chunk size,
deadline, stats adapter, or provider generation does not change analysis truth.

## 6. Budget, checkpoint, and request-control ports

### 6.1 Logical budgets

```simple
struct ProviderBudgetChargeV1:
    category: text
    amount: i64

trait ProviderBudgetPort:
    me charge(charge: ProviderBudgetChargeV1) -> Result<(), text>
    me charge_all(charges: [ProviderBudgetChargeV1]) -> Result<(), text>
    fn consumed(category: text) -> i64
    fn limit(category: text) -> i64

struct ProviderCheckpointProgressV1:
    stage: text
    bytes: i64
    events: i64
    scalars: i64
    hash_blocks: i64
    comparisons: i64

trait ProviderCheckpointPort:
    me checkpoint(progress: ProviderCheckpointProgressV1) -> Result<(), text>
```

The budget owner charges raw/decoded/output bytes, JSON events/depth,
normalization/case/token carry, tokens/terms/candidates/comparisons, logical
allocations, and durable-record growth before allocation or append. The
single-charge facade delegates to `charge_all`. Batch admission rejects an
empty batch, nonpositive amount, unknown category, duplicate-category sum
overflow, closed owner, or any exceeded limit before mutation; only after all
checks pass does the owner commit every aggregate counter atomically. The
session owner constructs one request-scoped checkpoint capability and binds the
validated `ProviderRequestControlHandleV1` exactly once. The checkpoint owner
validates per-step progress, queries the monotonic clock held by request
control, and returns only `cancelled`, `deadline_exceeded`, `limit_exceeded`, or
an internal clock/control failure. Algorithms receive only that bound
capability: they neither supply nor fabricate request identity and do not read
time or cancellation state through hidden globals.

### 6.2 Cancellation and commit admission

```simple
struct ProviderRequestControlHandleV1:
    request_id: text
    registration_generation: i64

struct ProviderCommitAdmissionPermitV1:
    request_id: text
    registration_generation: i64
    intent_hash: text
    permit_id: text

struct ProviderCancelResultV1:
    disposition: text
    target_request_id: text

trait ProviderRequestControlPort:
    me register(request_id: text, first_header_at_ms: i64,
                requested_deadline_ms: i64,
                intent_hash: text) \
        -> Result<ProviderRequestControlHandleV1, text>
    me cancel(cancel_request_id: text,
              target_request_id: text) \
        -> Result<ProviderCancelResultV1, text>
    me try_commit_admission(request: ProviderRequestControlHandleV1,
                            intent_hash: text) \
        -> Result<ProviderCommitAdmissionPermitV1, text>
    me complete(permit: ProviderCommitAdmissionPermitV1,
                outcome_hash: text) -> Result<(), text>
```

`register` rejects duplicate IDs, invalid 1..30,000 ms deadlines, timestamp
overflow, and deadlines already expired relative to the first header byte.
It computes and owns the absolute monotonic deadline. `cancel` only accepts a
fully decoded, canonical, host-bound cancel frame. Unknown target returns
`target_not_found`; cancel_requested, commit_admitted, or completed returns
`already_complete`; otherwise it transitions running/registered to
`cancel_requested` and returns `cancelled`.

`try_commit_admission` performs one atomic owner-local arbitration: validate
handle, intent hash, cancellation, current monotonic time, semantic deadline,
and request state, then transition to `commit_admitted` and issue a binding
permit. It occurs after response bytes/hash and commit intent are ready but
before journal write, fsync, rename, lifecycle CAS, or other side effect. The
permit closes only cancel/deadline eligibility; it is not evidence that any
semantic mutation has linearized or become durable. `index_apply` still
linearizes at durable candidate creation, and every terminal `index_publish`
outcome still linearizes in the combined terminal transaction defined by the
search-provider design. Once granted, cancel/deadline cannot relabel the
admitted operation. `complete` validates the same permit, records the outcome
hash exactly once, and transitions to completed.

Output uses a separate transport deadline. A timeout/EOF/error after complete
may close the transport, but a durable mutation remains discoverable by replay.

## 7. Resumable work and session ownership

### 7.1 Work machine

```simple
struct ProviderStepLeaseV1:
    limits: ProviderStepLimitsV1
    request: ProviderRequestControlHandleV1

struct ProviderCommitIntentV1:
    kind: text
    base_etag: text
    base_logical_root: text
    candidate_uid: text
    canonical_lifecycle: ProviderSegmentedBytesV1
    intent_hash: text

struct ProviderWorkProductV1:
    response_plan: ProviderResponsePlanV1
    commit_intent: ProviderCommitIntentV1?
    result_hash: text

struct ProviderWorkStepV1:
    kind: text
    product: ProviderWorkProductV1?
    error_code: text

trait ProviderWorkMachineV1:
    fn request_id() -> text
    me step(lease: ProviderStepLeaseV1,
            budget: ProviderBudgetPort,
            checkpoint: ProviderCheckpointPort) -> ProviderWorkStepV1
```

A machine owns only its typed request, immutable snapshot pin, local cursors,
bounded scratch, and child-created results. It cannot own or mutate
`SpipeProviderServiceV1`, durable storage, transport, request registry, or
receipt keys. `continue` means the stated lease is consumed or the next safe
yield was reached. `ready` moves one product to the owner. `failed` contains a
closed internal error code and no partial authoritative result.

Separate machine implementations cover initialize/open, search, explain,
stats, index apply, index publish, cancel, and shutdown. Search scoring caches
field tokens/lengths/term frequencies and corpus statistics; it must not retain
the existing repeated whole-field analysis inside document/term loops.

### 7.2 Sole session owner

```simple
class ProviderSessionOwnerV1:
    # private: service, stream/frame/json/response state, request control,
    # bounded FIFO/bytes, active work, output queue, budgets, stats/metrics
    static fn configured(service: SpipeProviderServiceV1,
                         control: ProviderRequestControlPort,
                         limits: ProviderLimitContractV1,
                         stats: ProviderProcessStatsPort) \
        -> Result<ProviderSessionOwnerV1, text>
    me run_tick(stream: ProviderByteStreamPort) \
        -> Result<ProviderSessionTickV1, text>
    fn finished() -> bool
```

`run_tick` performs the nine bounded reactor phases in the focused
architecture. It owns one active data machine. Fully validated cancel and
shutdown control envelopes are handled before the next data work step; other
envelopes enter a FIFO containing exactly zero through 16 queued ordinary
requests and bounded independently by encoded bytes. The active request is not
counted as one of the 16 queue entries. A 17th queued request (the 18th ordinary
request including the active one) receives bound `limit_exceeded`. FIFO full
applies transport backpressure, never unbounded buffering or data-request
reordering.

When a product is ready, the owner authorizes/signs its response plan, emits
bounded canonical segments and exact response hash, checkpoints, calls
`try_commit_admission`, validates the permit against the product/commit intent, then
executes the commit. Mutation commit uses the existing bounded conflict policy:
no unbounded retry; durable replay/reload decides an observed winner; unresolved
final CAS quarantines according to the lifecycle design. Commit admission is
always before fsync/CAS. After commit, `complete` and output enqueue occur.

The session remains one execution domain. If a future host uses reader/writer
threads, it must move immutable byte/control events through bounded mailboxes;
the session/service owner remains singular and worker results remain
owner-validated. Shared mutable service references are forbidden.

## 8. Process statistics capability

```simple
struct ProviderProcessStatsCapabilitiesV1:
    contract_version: text
    sample_monotonic_time: bool
    current_rss_bytes: bool
    peak_rss_bytes: bool
    user_cpu_ns: bool
    system_cpu_ns: bool

struct ProviderProcessStatsSampleV1:
    sampled_at_monotonic_ms: i64?
    current_rss_bytes: i64?
    peak_rss_bytes: i64?
    user_cpu_ns: i64?
    system_cpu_ns: i64?

trait ProviderProcessStatsPort:
    fn capabilities() -> ProviderProcessStatsCapabilitiesV1
    me sample() -> Result<ProviderProcessStatsSampleV1, text>
```

Each optional value must agree with its capability bit, be nonnegative, and use
the named unit. Unsupported is `nil` plus false, never zero plus true. The
protocol 1.0 `stats` capability remains true only when its required
`peak_rss_bytes` field is measured; later negotiated minors may expose the
closed per-field capability map. Linux, FreeBSD/macOS, and Windows adapters live
behind the common host facade and may use their native process APIs; app code is
identical.

Sampling is rate-limited and cached with timestamp, provider generation, and
adapter identity. `stats` reads the latest allowed sample and reports its age
in a negotiated minor; it never shells out or scans other processes. Logical
allocation accounting and an external supervisor enforce memory limits. RSS
does not authorize an allocation because it is process-wide and delayed.

## 9. Deadline, I/O, and commit sequence

```text
first header byte
  -> ingress frame/UTF-8/JSON/schema work (ingress + semantic time)
  -> register typed request (deadline remains header-relative)
  -> bounded work steps, control drain between steps
  -> response plan + canonical segmented response + hash
  -> final checkpoint
  -> ProviderRequestControlPort.try_commit_admission
  -> journal/fsync/CAS or read-result acceptance
  -> complete
  -> framed output using independent output deadline
```

The minimum semantic deadline is exactly 1 ms. Expiry is checked at each
checkpoint and at `try_commit_admission`; cooperative overshoot is bounded by the
qualified maximum checkpoint gap, not claimed to be zero. Ingress timeout may
fire before a full request exists and therefore closes silently. Output timeout
cannot roll back or relabel a completed operation.

A cancel arriving before commit-admission arbitration wins once its complete
frame is validated. A cancel arriving after permit issuance returns
`already_complete`; the permit itself is not the durable mutation
linearization point.
A fake stepping clock can test state transitions, but only a real framed cancel
through `ProviderByteStreamPort` proves negotiated cancellation.

### 9.1 Typed response-plan and emitter contract

`src/app/spipe_knowledge_provider/response_plan.spl` exclusively defines
`ProviderResponsePlanV1`. It stores a flat immutable tape of closed typed
instructions and its validated instruction/encoded-step ceilings. Typed
operation builders alone may create plans. They prevalidate exact schema field
order, UCD-17 NFC UTF-8 key order, duplicate keys, safe integers, and all
operation limits before returning a plan. The tape admits no map, `any`, raw
JSON fragment, recursive value, caller-controlled punctuation, or join-based
buffer.

Protocol 1.0 caps a plan at 262,144 instructions. A step consumes at most 256
instructions and emits at most 4,096 bytes, with stricter positive operation
limits allowed. These are hard maxima, not scheduler suggestions.

`ProviderCanonicalJsonEmitterV1` owns the only tape cursor. One bounded step
returns exactly `continue`, `ready`, or `failed`, emits no more than the granted
work/output limits, and keeps total segmented staging at or below
`maximum_output_bytes`. For every accepted output chunk it appends and hashes
the identical `(bytes, offset, count)` slice and then checkpoints. The design
does not claim rollback or zero-copy behavior.

The first sink, SHA, budget, or checkpoint failure is terminal and stable.
Later step/take/digest calls return that failure without progress. Partially
written internal segments and partially advanced SHA state are unpublishable,
are discarded with the failed emitter, and cannot be retried or taken. Only a
`ready` result authorizes exactly one move of both completed segmented bytes and
digest to the session owner; subsequent calls report emitter completion.

## 10. Startup, hot path, memory, and invalidation

### 10.1 Startup

Startup performs configuration/schema/limit validation, lifecycle recovery,
host-binding and authority construction, stats-capability discovery, fixed
segment allocation, and one session-owner construction. It does not parse the
tree, analyze the corpus, copy Unicode tables, start a per-request process, or
claim cancellation before the byte reactor is selected.

The protocol-1.0 handshake preserves its existing closed
implementation/analyzer/table/score/explanation/logical-index digests and exact
`cancel:true, stats:true` capability shape. This slice does not add queue,
pending-byte, transport-timeout, step, checkpoint-gap, or supervisor-limit
fields. Those remain host-local configuration and payload-free qualification
evidence until an explicit compatible protocol minor defines a closed extension
schema and vectors. Startup remains within the parent provisional 250 ms P95
target after Wave-0 profile lock.

### 10.2 Hot paths

No hot request may:

- convert the complete raw frame to `text` before validation;
- call recursive/whole-tree JSON parse or serializer;
- concatenate/join an unbounded response;
- run one-shot SHA/NFC/lowercase over an unbounded value;
- reanalyze every corpus field inside every document/term score loop;
- read a filesystem tree, shell out, launch a process, or sleep-retry;
- sample OS statistics on every inner step;
- perform any commit I/O before final commit-admission arbitration.

Request memory is bounded by one decoder staging chunk + cumulative FIFO encoded bytes
+ typed admitted values + one work machine/scratch + one segmented response +
declared lifecycle candidate allocations. Allocation is charged before growth.
The Wave-0 scale profile records current/peak RSS and locks an absolute release
budget; implementation may not replace missing RSS with zero or omit it from
evidence.

### 10.3 Observability

Required safe metrics are per-stage elapsed/cpu where supported, byte/event/
scalar/hash-block/comparison counts, checkpoint-gap distribution, request-state
transitions, real cancel arrival-to-observation, commit-admission winner and
later durable mutation linearization identity, FIFO
depth/bytes/backpressure, short/timeout/EOF/error I/O, output segments/bytes,
cache hit/miss/invalidation, logical allocation, stats support/sample age, and
current/peak RSS where supported.

Metrics and logs must not contain raw frames, payloads, query/document text,
normalized scalars, tokens, secrets, receipt seeds/signatures, cursor bodies,
or unredacted request IDs. Use operation class, counts, safe scope hashes, and
independent correlation IDs.

## 11. Migration subwaves

These subwaves refine parent Wave 4 and precede any accepted `cancel:true`.

### Wave 4S-A — Truth and evidence baseline

- Freeze protocol 1.0 request/response bytes and current `cancel:false`.
- Measure whole-frame/parser/analyzer/SHA/emitter spans, checkpoint gaps,
  transient allocation, startup/query latency, and RSS support.
- Add no semantic behavior.
- **Gate:** current capability and unavailable-field claims match runtime.

### Wave 4S-B — Raw byte transport and framing

- Add the `app.io` byte capability and provider fail-closed normalization.
- In a separate prerequisite runtime-owner lane, add the pollable raw-byte
  inherited-stdio primitive and bind it through a concrete `app.io` adapter;
  do not emulate deadlines around blocking reads.
- Add `ProviderByteStreamPort`, decoder header/payload events, encoder,
  segmented output, and ingress/output deadlines behind the synchronous
  behavior adapter. The decoder emits at most one bounded owned payload chunk; it
  never accumulates a complete payload.
- Exercise short, zero/would-block, timeout, EOF, and error outcomes.
- **Gate:** capability plus normalization alone is PARTIAL. Completion also
  requires the concrete adapter on the admitted runtime; every protocol 1.0
  golden frame is byte-identical; malformed,
  oversize, incomplete, and invalid prebinding input closes silently.

### Wave 4S-C — Iterative JSON and incremental SHA

- Add UTF-8 lexer, explicit JSON stack, typed envelope builders, iterative
  emitter, flat immutable response plan, segmented sink, and streaming SHA.
- Make `response_plan.spl` the sole plan owner. Typed schema builders must
  prevalidate ordered NFC UTF-8 keys and safe integers; the emitter owns one
  cursor and exposes only `continue | ready | failed`. Reject maps, `any`, raw
  fragments, recursion, joins, and staging above `maximum_output_bytes`.
- Terminally latch sink/SHA/budget/checkpoint failure. Partial internal
  sink/hash state is discarded and permits no retry, take, or digest; only
  `ready` publishes both outputs. Do not claim rollback or zero-copy.
- Keep whole-value compatibility facades outside the provider hot path.
- Exercise UTF-8 with every single split and deterministic mixed/random
  partition sequences through two-, three-, and four-byte scalars and
  combining sequences. Reject negative offset, negative count, and
  `offset > bytes.len` at every byte-slice boundary before reading or charging
  bytes, producing output, or mutating UTF-8 carry/SHA buffered or compressed
  content. Rejection terminally latches the exact range-error reason; every
  subsequent update/finalize call fails with that recorded reason. No semantic
  bytes are consumed and no digest is published by the rejected call.
- Exercise SHA at 0, 1, 55, 56, 63, 64, and 65 bytes at every single split.
  Exercise 4,095, 4,096, 4,097, and 1,048,576 bytes at exact
  block/quantum/end boundaries plus multiple deterministic fixed-seed
  irregular partitions crossing SHA block boundaries. Stream frozen
  receipt/replay/candidate/payload and domain-input preimages through their
  authoritative exported builders, with exact digest/canonical-byte parity
  and charge/checkpoint failures that leave no published digest.
- **Gate:** canonical/error/digest parity for every required partition and
  vector; bounded depth/tokens/bytes prove before allocation; the post-fix
  focused tests execute and PASS. Static correction or review alone cannot
  close the gate.
- **Current status:** work-control is accepted and pushed; request-control has
  a fresh focused PASS 9/9; and UTF-8 has a fresh focused PASS 7/7. The accepted
  reusable-schedule optimization has 4,097-byte full-versus-bounded parity and
  a cycle-3 bounded guard-probe PASS at 1.26 s/43,852 KiB. The full qualified
  1-MiB `W4-SRCH-31` oracle remains `FAIL`; these focused results do not prove
  the integrated pipeline, so Wave 4S-C is open.

### Wave 4S-D — Streaming analyzer and lexical cache

- Add split-safe NFC/lowercase/NFC/token states, Final_Sigma context, analyzer
  limits, analyzed-field cache, corpus-stat/posting invalidation.
- Route batch facade through streaming only after parity.
- **Gate:** UCD-17 corpus and every chunk split match batch bytes/tokens/
  positions; excessive carry fails bounded; score/explanation parity holds.

### Wave 4S-E — Read-only work machines

- Convert initialize/open/search/explain/stats/unsupported operations to
  `ProviderWorkMachineV1.step` and one-owner reactor.
- Measure work/checkpoint limits and preserve response ordering.
- **Gate:** no unbounded call exists between checkpoints; 1 ms deadline fixture
  is admitted and resolved honestly; legacy bytes remain identical.

### Wave 4S-F — Mutation machines and control arbitration

- Convert apply/publish/lifecycle paths to child-created commit intents.
- Add request register/cancel/try-commit-admission/complete, bounded FIFO, and
  final eligibility arbitration before journal/fsync/CAS.
- **Gate:** actual same-stream framed cancel interrupts a long request before
  commit admission; before/after-permit races are deterministic; durable
  candidate creation and the combined terminal transaction remain the only
  mutation linearization points; crash/replay and CAS/quarantine evidence
  remains valid. Synthetic clock alone is insufficient.
- Only after this gate may the qualified host advertise `cancel:true`.

### Wave 4S-G — Cross-platform statistics

- Add capability/sample port and host adapters; remove app platform branching.
- Preserve protocol 1.0's required peak-RSS shape; negotiate extensions.
- **Gate:** supported fields are measured with correct units on each admitted
  OS; unavailable remains false/nil and never passes an RSS gate.

### Wave 4S-H — Integration and optimization

- Lock measured step/profile limits, cache behavior, startup/query latency,
  max RSS, and external supervisor evidence.
- Remove provider hot-path compatibility routing only after focused high-model
  review and admitted runtime evidence.
- **Gate:** full provider golden/parity/lifecycle/transport/performance suite,
  direct-env guards, source checks, and highest-capability review pass.

## 12. Verification design and shared helper names

The implementation plan must use these shared scenario/helper names before
parallel test lanes fan out:

- `setup_streaming_provider_session`
- `send_provider_frame_chunks`
- `send_provider_cancel_frame`
- `collect_provider_frame_chunks`
- `assert_provider_transport_closed`
- `assert_provider_bound_response`
- `assert_provider_admission_and_linearization_winner`
- `measure_provider_checkpoint_gap`
- `measure_provider_process_stats`

Any unavailable oracle starts with `fail("streaming provider oracle not
implemented")`; placeholder passes are forbidden.

Required evidence includes:

| Concern | Evidence |
|---|---|
| raw framing | every header/payload split, coalesced frames, short/zero/would-block read/write, timeout/EOF/error; exactly one header event precedes contiguous nonempty bounded owned payload chunks; concatenated chunk bytes equal the declared payload once with no gap/overlap/replay; completion returns metadata only |
| prebinding safety | oversize, malformed header, invalid UTF-8, noncanonical JSON silently close with no reflected content |
| iterative JSON | depth/token/member/string limits, duplicate/out-of-order keys, integer/escape canonicality, no recursion; typed flat response-plan instruction/step ceilings; schema-builder rejection of non-NFC/out-of-order/duplicate keys and unsafe integers before emission; identical append/hash chunks; terminal sink/SHA/budget/checkpoint faults leave partial state unpublishable; only `ready` permits one take/digest |
| incremental SHA | state owns eight digest words, one partial 64-byte block, and one fixed reusable owner-local 64-word message schedule that remains O(1), is never passed/returned, and is not reallocated per block; this is not a zero-copy claim; lengths 0/1/55/56/63/64/65 exercise every single split; 4095/4096/4097/1 MiB exercise exact block/quantum/end boundaries plus multiple deterministic fixed-seed irregular partitions crossing SHA block boundaries; frozen receipt/replay/candidate/payload and domain-input preimages flow through their authoritative exported builders, and every partition preserves exact digest/canonical-byte parity rather than merely comparing a one-shot output; negative offset/count and `offset > len` reject before reading/charging bytes, output, or buffered/compressed-content mutation, terminally latch the recorded range reason, and make later update/finalize calls fail with that reason; no semantic bytes are consumed or digest published by rejection; charge failure prevents its compression, while checkpoint failure terminalizes the stream without digest publication and need not roll back prior compressed state; 4,097-byte full-versus-bounded parity and the cycle-3 guard-probe PASS at 1.26 s/43,852 KiB are bounded optimization evidence only; acceptance still requires the full qualified 1-MiB post-fix PASS |
| incremental UTF-8 | every single split plus deterministic mixed/random partition sequences preserve valid decoded bytes; negative offset/count and `offset > len` reject before reading/charging bytes, output, or carry mutation, terminally latch the recorded range reason, and make later update/finalize calls fail with that reason; no semantic bytes are consumed; malformed/truncated input fails identically in an executed post-fix PASS |
| Unicode | NFC split sequences, Hangul, combining reorder/compose, U+0130 expansion, Final_Sigma lookahead across chunks, long carry failure |
| analyzer/search | token/position/length/TF/corpus-stat/score/order/explanation parity and targeted invalidation |
| deadline | exact 1 ms minimum, header-relative expiry during ingress/parse/work/emission, measured checkpoint overshoot |
| cancellation | real framed cancel before commit-admission permit, cancel after permit, unknown/duplicate target, FIFO/backpressure; fake clock cannot qualify |
| commit | eligibility arbitration precedes journal/fsync/CAS but is not mutation linearization; durable candidate creation or the combined terminal transaction is the semantic point; crash at every post-permit durability phase recovers/replays truth |
| output | deadline/EOF/error after completed mutation does not relabel durable outcome |
| stats | capability/value/unit parity on Linux, FreeBSD/macOS, Windows and explicit unsupported behavior |
| privacy | logs/metrics contain no raw payload/query/document/token/secret/cursor data |
| performance | startup, exact/search latency, checkpoint gaps, logical allocation, current/peak RSS and cache invalidation on Wave-0 fixture |

High-capability review must inspect the actual call graph and prove that every
advertised cancellable/deadline-aware operation reaches only bounded step
implementations. Finding calls to whole-frame text conversion, recursive JSON,
one-shot unbounded analyzer/hash/emitter, hidden OS reads, or commit I/O before
arbitration is release-blocking.

## 13. Requirement trace

| Requirement | Design evidence |
|---|---|
| REQ-SPKC-013 | raw bounded provider protocol, untrusted typed decode, explicit capabilities |
| REQ-SPKC-014 | common streaming analyzer/SHA/search contracts and bounded work |
| REQ-SPKC-015 | cancellation/query-budget/stat ports reusable by all DB tiers |
| NFR-SPKC-001–002 | chunk partition, provider, and incremental/cache parity |
| NFR-SPKC-003–004 | protocol 1.0 compatibility, honest capability fallback/fail-closed boundaries |
| NFR-SPKC-011 | exact byte/event/depth/carry/result/FIFO/work/time/memory bounds |
| NFR-SPKC-012–013 | analyzer/score/explanation and exhaustive/optimized parity retained |
| NFR-SPKC-014–016 | startup/update/search/checkpoint/RSS qualification and compatibility regression evidence |
| NFR-SPKC-019 | one app/host capability ports and protocol/client compatibility |
| NFR-SPKC-021–022 | reproducible evidence and least-authority module boundaries |
| NFR-SPKC-025 | bounded verify/fix cycles plus independent highest-capability acceptance |

## 14. Streaming-SHA performance status

The Wave 4S-C SHA gate is `FAIL`. Interpreter verification cycle 2 produced no
result and was terminated at about 3:09 after the 180-second ceiling. Remove
scale-sensitive value-array copies through an owner-local fixed block and
bounded immutable byte-loan path; profile fixture, reference, update, and
compression separately. Do not shrink the required 1 MiB oracle. See
`doc/08_tracking/bug/spipe_streaming_sha_interpreter_value_array_copy_timeout_2026-08-25.md`.

The subsequent contract-complete nine-scenario run after the bounded
optimization reached the exact 180-second ceiling, exited `124`, and emitted
no summary. Its resolved executable was
`/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`
(`Simple Language v1.0.0-RC`, SHA-256
`3ef64bffc68d0b1c2dd851d1f02976ca98fba6f88fbb406dddf56ba7f3ca27c0`),
but the wrapper classified it as a Rust-built bootstrap seed rather than an
admitted Stage 4 artifact. `/usr/bin/time` died with the process, so this run
has no RSS measurement. It is separate from the earlier approximately 3:09
uncontrolled run. Complete-matrix static high review is done, but no candidate
matrix files are accepted and the full gate remains `FAIL`.

Before another execution, add a bounded, payload-free stage progress receipt
that identifies fixture, reference, update/compression, checkpoint, and final
emission progress, or acquire a provenance-qualified pure-Simple Stage 4
executable and run the unchanged matrix. Do not extend the timeout, reduce the
1-MiB workload, relabel the matrix as ten scenarios, or infer an RSS value.

## 15. Iterative canonical-JSON candidate status

The fresh focused cycles ended at `2/5`, `1/8`, and `7/8`. The remaining
executed failure is the nested-value test expression `.unwrap().bytes()`, so
the run does not establish either a product failure or a PASS. No decoder,
focused-spec, or dependency file from this candidate is accepted.

Before consuming or hashing a byte slice, the decoder must validate its range,
budget, and canonicality preconditions; the authoritative raw-byte cursor may
advance only afterward. Likewise, the event's complete multi-category charge
must be reserved atomically before mutation of the container stack, root
result, or emitted-event state. The candidate's `streaming_sha256`
`Result`-wrapper fix is an unaccepted dependency and must not be folded into
JSON acceptance implicitly.

The exact fresh-session sequence is: bind the nested `unwrap()` result to a
local before requesting `bytes()`; run the unchanged eight-case focused spec
once; if and only if it passes, perform highest-capability call-graph review of
validation-before-SHA/cursor and reservation-before-mutation; then accept the
decoder, spec, and any independently qualified SHA dependency as explicitly
scoped units. Until then this design lane is `IN PROGRESS`.

## 16. Canonical response-emitter candidate status

This lane is `IN PROGRESS`. Cycle 1 encountered a parser failure, which was
fixed without producing an executed behavioral result. Cycle 2 passed `5/5`
on the earlier pre-ownership draft, but subsequent highest-capability review
returned structural `FAIL`: capability ownership and terminal publication did
not satisfy the frozen contract. Neither the green count nor its source/spec is
accepted.

The redesigned emitter owns its segmented sink, SHA stream, budget, and
checkpoint. Its typed builder rejects forged plans, and configuration verifies
the exact predicted output size against the bounded plan before emission. SHA
must finalize successfully before transition to `ready`; only `ready` permits
one `take_ready`, after which neither bytes nor digest can be taken again.
Cycle 3 executed `0/5` because a nested `.bytes()` test expression hit a
compiler limitation. That expression was mechanically split into a local
after the run and has not been executed. No candidate emitter source or focused
spec is accepted.

In a fresh session, execute the unchanged five-case focused spec once. A full
PASS then requires highest-capability call-graph review of forged-plan and
exact-size prevalidation, exclusive capability/cursor ownership, byte-identical
sink/SHA input, checkpoint order, failure latching/discard, finalize-before-
ready, and exactly-once take. Decoder `7/8` and SHA `W4-SRCH-31 FAIL` remain
unchanged and non-transitive.

### 16.1 Subsequent decoder/emitter evidence

Decoder cycle 3 later executed `PASS 8/8`, but call-graph high review returned
`FAIL`. A new `transport_bytes` counter is a parallel cursor: incomplete C2
input reports consumed/transport progress while raw-byte and SHA cursors do not
advance together. This violates the single-cursor, exact consumed-prefix hash
design. Value-semantic rollback is improved, but decoder source/spec remains
unaccepted.

The emitter's fresh bounded cycles produced `2/5`, `2/5`, and `4/5`. Its
post-cap second-take correction has not executed. High review found no exact
predicted-output-size validation, scratch-cursor mutation before sink/SHA/
checkpoint acceptance, and no complete first/middle/final or cap-boundary fault
matrix. Emitter source/spec remains unaccepted. Wave status is `IN PROGRESS`;
the independent SHA gate remains `W4-SRCH-31 FAIL`.

### 16.2 V2 closure evidence

Decoder v2 produced `PASS 8/8` for all three permitted cycles. Its central
single cursor and trial transition pass structural inspection, but final high
review is `FAIL`: the escape oracle verifies lengths rather than exact values,
token/member limits use seeded counters instead of cumulative real input, some
failure classes do not prove identical terminal results from `push`,
`next_event`, and `finish`, and the executable has bootstrap-seed provenance.
No source/spec is accepted.

Emitter v2 produced `1/8`, `8/8`, and `11/11`. The candidate repairs trial
cursor/child-copy behavior, exact-size/cap/fault mechanics, and member close.
It still lacks an immutable global `maximum_output_bytes <= 1,048,576` rule;
payload, page, and explanation maxima are caller-selected rather than fixed to
1,048,576, 524,288, and 65,536 bytes; and exported generic/raw constructors
permit bypass of typed schema builders. Its execution also used bootstrap-seed
provenance. Final high review is `FAIL`; no files are accepted. Overall status
is `IN PROGRESS`, with `W4-SRCH-31 FAIL` unchanged.
