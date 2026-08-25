<!-- codex-architecture -->
<!-- codex-design -->
# SPipe Knowledge Compiler — Cooperative Streaming Provider Architecture

**Status:** Normative focused extension to the accepted architecture
**Date:** 2026-08-25
**Parent architecture:** `spipe_knowledge_compiler.md`
**Detail design:** `../../../05_design/infra/spipe/spipe_knowledge_compiler_cooperative_streaming.md`
**Requirements:** REQ-SPKC-013–015; NFR-SPKC-001–004, 011–016, 019, 021–022, 025

## 1. Decision

The provider host becomes a bounded, single-owner reactor. It retains protocol
1.0's eight-lowercase-hex-byte length prefix and one logical canonical-JSON
frame, but raw transport data remains `[u8]` until incremental UTF-8, JSON, and
operation-schema validation completes. One `ProviderSessionOwnerV1` owns the
transport cursors, frame decoders/encoders, request-control registry, one active
`ProviderWorkMachineV1`, a bounded FIFO, and the mutable
`SpipeProviderServiceV1`.

Long operations are explicit resumable state machines. The session owner
alternates bounded transport progress, validated control-frame processing, one
bounded work step, and bounded output progress. No hidden one-shot parser,
normalizer, hasher, scorer, serializer, blocking read, or blocking write may be
described as cooperatively cancellable.

The stable architecture names are:

- `ProviderByteStreamPort`
- `ProviderFrameDecoderV1`
- `ProviderFrameEncoderV1`
- `ProviderRequestControlPort`
- `ProviderWorkMachineV1.step`
- `ProviderSessionOwnerV1`

Adapters and later protocol minors may extend records, but may not create
parallel semantic owners or bypass these boundaries.

## 2. Current-state gap

The present `src/app/spipe_knowledge_provider/main.spl` reads the complete
payload, converts it to `text`, and synchronously dispatches it before reading
another frame. `wire_dispatch.spl` then uses whole-input JSON parsing and
canonical re-emission. `wire_json.spl`, `lexical.spl`, the common analyzer, and
SHA helpers contain whole-value operations whose callers can only checkpoint
before and after the call. Consequently, an inner clock poll does not make the
whole call interruptible, and the same stdio loop cannot observe a later cancel
frame while a request executes.

The current initialization response therefore correctly advertises
`"cancel":false`, and `cancel` returns `unsupported_capability`. Any document,
test, or response claiming `cancel:true` before this architecture's control-path
and checkpoint-gap gates pass conflicts with runtime truth and must fail
verification. The migration changes capability truth, not protocol 1.0 framing.

## 3. Architectural invariants

1. `ProviderSessionOwnerV1` is the only mutable session and service-state owner.
2. The byte-stream adapter owns OS handles; it returns owned byte chunks and
   receives scoped byte loans. It never parses JSON or mutates provider state.
3. Frame and JSON machinery operates on bytes. Text exists only after strict
   incremental UTF-8 validation and typed field admission.
4. One active data operation and exactly 16 queued ordinary requests are the
   complete data-operation concurrency bound. Validated
   cancel and shutdown controls may bypass the data FIFO; ordinary operations
   may not reorder.
5. A work step has a deterministic work-unit ceiling. The reactor regains
   control after every step and drains validated control input before the next.
6. Semantic deadlines start when the first header byte is accepted. Parse,
   validation, normalization, hashing, execution, and response construction
   are included. Ingress-stall and output-stall deadlines are separate
   transport policies.
7. `ProviderRequestControlPort.try_commit_admission` is the sole
   cancel/deadline eligibility decision before commit work begins. Before it
   succeeds, cancel/deadline wins. After it succeeds, cancel/deadline cannot
   relabel the admitted operation. This control permit is not a semantic
   mutation linearization point: `index_apply` linearizes only when durable
   candidate creation commits, and a terminal publish outcome linearizes only
   in its combined terminal transaction.
8. Canonical JSON decoding, emission, SHA-256, NFC, default lowercase, and
   tokenization are invariant under every legal input chunk partition.
9. Memory correctness is enforced by logical allocation budgets and bounded
   containers. Sampled RSS is evidence, not an allocation authority.
10. Platform-specific clocks, byte I/O, and process statistics remain behind
    host capability ports. Application logic contains no OS branches.

## 4. MDSOC ownership and composition

```text
ProviderSessionOwnerV1 (sole session/service mutable owner)
├── ProviderByteStreamPort          host I/O capability adapter
├── ProviderFrameDecoderV1          ingress framing state
│   └── Iterative canonical JSON pipeline
├── ProviderRequestControlPort      request lifecycle authority
├── ProviderWorkMachineV1           one request-local resumable machine
│   ├── streaming SHA transform
│   ├── streaming Unicode analyzer transform
│   └── operation-specific search/index/stat work
├── SpipeProviderServiceV1          snapshot/lifecycle truth
├── 16-entry ordinary-request FIFO owned typed envelopes
└── ProviderFrameEncoderV1          bounded segmented output
```

### 4.1 Normative provider interfaces

This section is the signature authority for every plan, test, and implementation
lane. Unversioned aliases such as `FrameDecoder`, `Encoder`, `RequestControl`,
`WorkMachine`, and `SessionOwner` are not contracts.

```simple
ProviderByteIoStatusV1 = data | timeout | eof | error

trait ProviderByteStreamPort:
    me read_some(maximum_bytes: i64,
                 deadline_at_ms: i64) -> ProviderByteReadV1
    me write_some(bytes: [u8], offset: i64, maximum_bytes: i64,
                  deadline_at_ms: i64) -> ProviderByteWriteV1

class ProviderFrameDecoderV1:
    static fn configured(limits: ProviderTransportLimitsV1) \
        -> Result<ProviderFrameDecoderV1, text>
    me push(bytes: [u8], offset: i64, observed_at_ms: i64) \
        -> ProviderFrameDecodeStepV1
    me take_complete() -> Result<ProviderFrameCompletionV1, text>

class ProviderFrameEncoderV1:
    static fn configured(payload: ProviderSegmentedBytesV1,
                         limits: ProviderTransportLimitsV1) \
        -> Result<ProviderFrameEncoderV1, text>
    fn complete() -> bool
    fn next_write(maximum_bytes: i64) -> ProviderFrameWriteLoanV1
    me advance(written_bytes: i64) -> Result<(), text>

trait ProviderRequestControlPort:
    me register(request_id: text, first_header_at_ms: i64,
                requested_deadline_ms: i64, intent_hash: text) \
        -> Result<ProviderRequestControlHandleV1, text>
    me cancel(cancel_request_id: text, target_request_id: text) \
        -> Result<ProviderCancelResultV1, text>
    me try_commit_admission(request: ProviderRequestControlHandleV1,
                            intent_hash: text) \
        -> Result<ProviderCommitAdmissionPermitV1, text>
    me complete(permit: ProviderCommitAdmissionPermitV1,
                outcome_hash: text) -> Result<(), text>

trait ProviderWorkMachineV1:
    fn request_id() -> text
    me step(lease: ProviderStepLeaseV1,
            budget: ProviderBudgetPort,
            checkpoint: ProviderCheckpointPort) -> ProviderWorkStepV1

class ProviderSessionOwnerV1:
    static fn configured(service: SpipeProviderServiceV1,
                         control: ProviderRequestControlPort,
                         limits: ProviderLimitContractV1,
                         stats: ProviderProcessStatsPort) \
        -> Result<ProviderSessionOwnerV1, text>
    me run_tick(stream: ProviderByteStreamPort) \
        -> Result<ProviderSessionTickV1, text>
    fn finished() -> bool
```

`ProviderByteReadV1` and `ProviderByteWriteV1` each carry the closed four-state
status above. Positive progress is `data`; zero-byte would-block is `timeout`,
never data. Both calls carry absolute transport deadlines. A
`ProviderRequestControlHandleV1` binds request ID and registration generation;
`ProviderCommitAdmissionPermitV1` repeats those fields and binds the exact
intent hash plus permit ID. `complete` accepts only that permit and the exact
outcome hash. The permit records that cancel/deadline eligibility arbitration
has closed; it does not claim that a candidate, terminal record, publication,
or other mutation is durable. The detail design may expand supporting record
fields, but it may not change these public operations.

`ProviderCheckpointPort` is a request-scoped capability constructed by the
session owner from that validated handle. Its leaf operation is
`checkpoint(progress: ProviderCheckpointProgressV1)`: algorithms never pass,
select, or fabricate request identity. Cancellation and monotonic-deadline
authority remain in request control, and a child work capsule cannot inspect a
sibling request.

Each `ProviderFrameDecodeStepV1` carries at most one closed event kind:
`none`, `header`, or `payload`. `header` is emitted exactly once after the
eighth header byte and before any payload byte is consumed. `payload` owns
a bounded immutable `ProviderFramePayloadChunkV1` with `bytes`, `offset`,
`count`, and absolute `frame_payload_offset`. The chunk is a fresh owner-created
result moved out of the decoder; the decoder retains no payload alias. The
declared length is absent only on a pre-header `none` event and exact on header
and payload events; the owned chunk is present only on a payload event. The
decoder's `payload_bytes_read` is the only framing cursor; the session advances
input only by `consumed_bytes` and never maintains a duplicate payload cursor.
`take_complete` returns only `ProviderFrameCompletionV1` metadata after all
declared bytes have been emitted and consumed; it never returns or accumulates
the payload.

The session is a virtual capsule. Budgets, cancellation, deadlines, metrics,
and audit are feature transforms around its ports and work steps. Frame, JSON,
Unicode, SHA, search, durable lifecycle, and statistics implementations are
adapters or child capsules. Siblings exchange immutable values or owner-created
results; none reaches into another sibling's private cursor, stack, carry,
hash state, snapshot, or lifecycle fields.

Boundary classifications are explicit:

| Boundary value | Ownership class |
|---|---|
| bytes returned by `read_some` | owned move into session/decoder |
| payload bytes emitted by decoder | bounded owned chunk moved from decoder result; no retained decoder alias |
| bytes passed to `write_some` | scoped read-only loan from encoder segment |
| admitted request envelope | owned typed value in bounded FIFO |
| pinned search snapshot | immutable frozen share |
| work-machine continuation | owner-local owned state |
| work product/commit intent | child-created owned result; owner validates |
| cancellation | validated control message applied by session owner |
| OS stream/process handle | opaque capability handle held by adapter |

No raw pointer, ambient file descriptor, generic `any`, OS name, or mutable
service reference crosses these boundaries.

## 5. Reactor, admission, and durable linearization model

Each reactor tick performs bounded work in this order:

1. Progress an incomplete header/payload read up to the ingress slice limit.
2. Progress iterative UTF-8/JSON/schema decode for available payload bytes.
3. Apply every completely validated cancel/shutdown control already available.
4. Admit at most one typed data envelope to the bounded FIFO.
5. If idle, register and activate the FIFO head against a pinned snapshot.
6. Call `ProviderWorkMachineV1.step` once with a bounded step lease.
7. On a ready work product, build bounded canonical response segments, perform
   the final checkpoint, and call `try_commit_admission`.
8. Owner-validate and commit the work product, call `complete`, and enqueue the
   encoded frame.
9. Progress output by one bounded `write_some` call.

The owner may perform additional zero-deadline input polls between steps, but
it may not spin or sleep-retry. `read_some` and `write_some` distinguish data,
timeout, EOF, and error. Timeout is a normal reactor outcome; EOF and error
follow the transport-close policy.

A short read/write with positive progress is `data` and advances only by its
reported count. A zero-byte result is never `data`: nonblocking would-block is
reported as `timeout` with a non-authoritative `would_block` detail, stream
closure is `eof`, and all other failures are `error`. The reactor performs at
most one retryable I/O attempt per direction per tick; it never busy-loops on a
short, zero, or would-block result.

The repository's current inherited-stdio surfaces are blocking text/character
operations. Piped-child helpers are scoped to owned children, conflate empty
read data with would-block/closure/failure, and accept no absolute deadline.
They cannot implement this port authoritatively. Raw transport therefore has
two separately gated lanes: capability plus provider normalization first, then
a runtime-owner pollable raw-byte primitive and concrete `app.io` adapter. The
primitive must preserve binary bytes, distinguish all four outcomes, and use
an absolute monotonic deadline. Until that second lane passes on the admitted
runtime, raw transport is partial. A clock check after a blocking call is not
deadline behavior and is forbidden.

A cancel frame remains ordered behind bytes already written by the client on
the same protocol 1.0 stream. The provider guarantees bounded reaction after
the complete canonical cancel frame has been validated, not before those bytes
arrive. Queue depth, pending-byte, ingress/output timeout, step, and checkpoint-
gap limits remain host-local configuration and payload-free qualification
evidence. They are not added to protocol 1.0's closed initialization schema;
making any of them wire-visible requires an explicit compatible protocol minor.

## 6. Deadline domains

Three clocks must not be conflated:

| Domain | Start | End | Failure meaning |
|---|---|---|---|
| semantic request | first header byte accepted | response segments ready and `try_commit_admission` succeeds | `deadline_exceeded` before commit admission |
| ingress transport | first header byte accepted | complete frame admitted or rejected | transport/frame timeout; no request truth admitted |
| output transport | first write attempt | complete frame written | transport failure; committed/replayable truth is unchanged |

After parsing `deadline_ms`, the semantic absolute deadline is calculated from
the recorded first-header timestamp, not from parse completion. If it is
already past, admission fails. The effective pre-commit-admission deadline is the
minimum of requested and policy maximum. Wall time moving backwards,
overflow, an unavailable monotonic clock, or an unbounded host call fails
closed and prevents advertising cooperative deadlines.

Protocol 1.0's normative minimum requested deadline remains **1 ms**. It is not
raised to make implementation easier. This is a cooperative admission/checkpoint
contract, not a promise that an OS schedules or flushes a response within one
millisecond; the negotiated checkpoint-gap evidence states the possible
overshoot honestly.

Durable mutation response bytes are constructed before commit admission. The
final checkpoint and `try_commit_admission` arbitration occur **before**
journal write, fsync, rename, compare-and-swap, or any other commit side effect.
This is only cancel/deadline eligibility admission; it is deliberately not
called linearization. For `index_apply`, semantic mutation linearization remains
durable candidate creation. For `index_publish`, every terminal outcome
linearizes in the existing combined terminal transaction. After a successful
permit, crossing the deadline cannot rewrite the admitted outcome to
cancellation, but the permit alone proves no durable mutation. If the provider
dies during bounded but non-interruptible durable write/fsync/CAS, startup
recovery and replay determine truth.
External supervisors may impose a hard process deadline, but that is a distinct
negotiated capability and never inferred from cooperative polling.

Malformed frame headers, declared oversize frames, invalid UTF-8, incomplete
EOF, and noncanonical JSON before a complete trusted request binding are
transport-local failures and close silently. They cannot be reflected as a
bound provider error because request ID, operation, workspace, snapshot, and
scope are not trustworthy. Only after complete typed envelope and host-binding
validation may schema, limit, cancellation, or deadline failures use the bound
wire-error envelope.

Specifically, `invalid_utf8` and `frame_too_large` are the closed, payload-free
local `TransportDiagnosticV1` classes. They are not `ProviderErrorV1` codes and
never authorize a fabricated `ProviderResponseV1` before request binding.

## 7. Streaming semantic transforms

### 7.1 Iterative canonical JSON

An explicit lexer cursor and container stack replace recursive whole-tree parse
and recursive canonical re-emission on the provider path. The decoder enforces
UTF-8, canonical integer lexemes, canonical escapes, no insignificant
whitespace, strictly increasing object keys, no duplicates, closed operation
schemas, maximum depth, token/member/element/string/decoded-byte limits, and
the declared frame length while consuming chunks. It emits typed request
records rather than an authority-bearing `any` tree.

The protocol-1.0 provider ceiling is exactly 16 simultaneously open object or
array containers, 262,144 lexical JSON tokens, and 65,536 aggregate members.
Each completed object name/value pair and each completed array element consumes
one aggregate-member unit, regardless of which container owns it. The next
token/container/member is rejected before allocation when it would cross its
ceiling. Per-operation schemas may configure stricter limits, never wider ones.

The emitter accepts typed records whose field order is fixed by schema. It
writes escaped UTF-8 bytes into bounded segments; it does not construct arrays
of strings and `join` them. A segmented buffer is necessary because protocol
1.0's length prefix precedes the payload. The response-byte ceiling bounds that
buffer, and the encoder computes the prefix from exact segment lengths.

`segmented_bytes.spl` is the target sole owner of
`ProviderSegmentedBytesV1`; the accepted sink consumes that shared value
contract. The unaccepted `frame_encoder.spl` still declares a parallel value
type, so encoder migration to this owner remains a red Wave 4S-C obligation;
the current import graph is not evidence of single ownership. Sink growth is capability-owned:
`ProviderByteSinkPort.append(bytes, offset, count, budget)` validates the
checked range and prospective total, then submits logical output bytes and the
exact new-segment allocation in one atomic `charge_all` batch before any
mutation or allocation. A rejected category, aggregate overflow, or later
category limit leaves every budget counter unchanged.
`ProviderSegmentedByteSinkV1.configured(segment_bytes, maximum_bytes)` rejects
nonpositive limits. `take` moves all bounded segments out and resets the sink
without retaining aliases. Callers may not precharge approximately and then
delegate unchecked growth.

### 7.2 Incremental SHA-256

SHA state owns eight working words, a partial 64-byte block, one fixed reusable
owner-local 64-word message-schedule workspace, and a checked total byte count.
The schedule remains O(1), is never passed or returned, and is not reallocated
per block; this is bounded reuse, not a zero-copy claim. Domain bytes, length
binding, and canonical payload bytes are fed in order. Construction accepts a
fixed raw-byte domain separator of at most 63
bytes so it cannot perform an unbudgeted compression. Updates charge one
`hash_blocks` unit immediately before each bounded block and checkpoint;
finalization pads the partial block, then charges and checkpoints each padding
compression without copying or rereading the whole payload. Chunk partition
never changes the digest. A rejected charge prevents that compression. A
checkpoint rejection terminalizes the stream and prevents digest publication;
already-compressed internal state need not roll back. A sink transform can
update SHA while JSON emits.

### 7.3 Streaming analyzer

The parity pipeline remains exactly:

```text
strict UTF-8 -> NFC -> Unicode default lowercase -> NFC
            -> UCD-17 token classification -> stop-word/position emission
```

NFC retains only the current canonical-combining sequence and flushes it when
the next starter closes the sequence. Default lowercase retains only the
context needed for conditional Final_Sigma, including a bounded run of
case-ignorable code points. The second NFC stage handles expansion output.
The tokenizer retains only the current token and emits positioned tokens at a
delimiter or EOF. Combining, case-context, and token carries have explicit
limits; exceeding one returns `limit_exceeded` rather than buffering without
bound or producing provider-specific analysis.

The generated Unicode version and generator digest remain part of analyzer and
cache identity. All chunk-split results must equal the current batch analyzer
for inputs within the declared limits before the streaming path becomes the
canonical implementation.

## 8. Statistics and resource authority

`ProviderProcessStatsPort` exposes a versioned field-capability bitmap and a
single-process sample with normalized byte/nanosecond units. Unsupported values
are absent with `supported:false`; zero means a measured zero only. No app
module branches on `platform_name`, reads `/proc`, calls a shell command, or
imports a private runtime extern.

The host adapter may expose current RSS, peak RSS, user/system CPU time, and
monotonic sample time independently. `stats:true` is advertised only for the
closed field contract actually supported on that host. A cached, timestamped
safe sample is read by the `stats` operation; collection is rate-limited and
never scans other processes. Capability and sample cache are invalidated on
provider generation/adapter change.

Logical allocation counters remain the enforcement source because RSS samples
are delayed, allocator-dependent, and process-wide. A separately configured
supervisor may advertise/enforce a hard RSS limit. Missing RSS evidence is
`unsupported`, never a successful zero or a silently skipped performance gate.

## 9. Startup, hot paths, cache, and invalidation

Startup validates limits and host capabilities, recovers lifecycle state,
constructs one session owner, allocates fixed-size decoder/encoder segments,
and opens the long-lived byte stream. It performs no corpus scan, Unicode-table
copy, provider subprocess per request, or eager response-cache build.

Hot paths allocate only bounded frame segments, explicit parser/carry stacks,
request-local work state, top-k/search structures, and output segments. Token
and field-stat caches are keyed by content hash, field/analyzer identity, and
scope. A document delta invalidates only changed document tokens, lengths,
postings, corpus aggregates, explanations, and affected candidate roots. An
analyzer/table/limit-contract change invalidates the complete lexical segment;
a transport or stats-adapter change invalidates no lexical truth.

Observability records ingress/semantic/output duration separately; bytes and
steps per decoder/analyzer/hash/work stage; checkpoint-gap work and time;
cancel received/validated/observed/commit-admission race and later durable
mutation linearization point; FIFO depth/bytes;
partial writes; budget failure stage; response segments; logical allocation;
stats field support/sample age; current/peak RSS when available; and provider
generation. It never records private payload text.

It also never records raw payload/frame bytes, query text, document text,
normalized scalars, tokens, secrets, receipt seed material, or unredacted
request/cursor IDs. Safe operation classes, counts, durations, capability
versions, scope hashes, and independently generated correlation IDs are
sufficient.

Qualification must retain the parent architecture's 250 ms startup, 20 ms
exact, 100 ms search, and RSS evidence goals. Streaming adds provisional gates:
one work step processes at most 4 KiB input/output bytes, 1,024 Unicode scalars,
256 JSON events, 64 SHA blocks, or 256 posting/comparison units (whichever
applies first); Wave 0 locks measured checkpoint-gap latency and final values.
The host's qualification report records the locked limits without changing the
protocol 1.0 capability response. No unmeasured claim of a hard wall-time bound
is permitted.

## 10. Migration decisions and gates

1. **Instrument truth:** keep `cancel:false`; record one-shot spans and current
   platform-stat capability without changing behavior.
2. **Raw framing:** introduce the byte-stream port and incremental frame
   decoder/encoder behind parity fixtures; protocol 1.0 bytes remain identical.
3. **Iterative JSON and SHA:** typed streaming decode/emission and incremental
   hashing replace provider hot-path whole-value calls only after executed
   byte/digest parity. UTF-8 qualification covers every single split plus
   deterministic mixed and randomized partition sequences across valid
   multi-byte scalars and combining sequences. Every byte-slice entry point
   rejects negative offset, negative count, and `offset > bytes.len` before
   reading. SHA qualification is exhaustive at every single split through 65
   bytes. For 4,095/4,096/4,097/1-MiB inputs it covers exact
   block/quantum/end-boundary partitions plus multiple deterministic fixed-seed
   irregular partitions crossing SHA block boundaries, rather than every
   possible large-input split. Frozen receipt/replay/candidate/payload and
   domain-input preimages flow through their authoritative exported builders;
   exact digest and canonical-byte parity remains mandatory. A source review
   or static correction without a post-fix executed PASS is not acceptance
   evidence.
4. **Streaming analyzer:** land split-invariant NFC/lowercase/NFC/token states
   and cache identity; retain batch facade until exhaustive parity passes.
5. **Work machines:** split read/search/explain/stats, then index mutations,
   into resumable owner-result machines. Durable commit remains parent-owned.
6. **Control reactor:** land request registration, cancel, commit admission,
   completion, bounded FIFO, and transport deadlines. Durable candidate or
   terminal transactions remain semantic mutation linearization. Only now may qualified
   hosts change the same protocol 1.0 capability to `cancel:true`.
7. **Portable stats:** replace platform-name branching with the capability port
   and cross-platform adapters; advertise only measured fields.
8. **Optimize:** cache/token/posting changes follow only after semantic, digest,
   lifecycle, response-byte, and checkpoint evidence is accepted.

Each stage is independently reversible. A failed parity or checkpoint gate
retains the preceding implementation and its honest capability response; it
does not create a compatibility fallback inside a new hot path.

Current Wave 4S-C evidence status is deliberately non-transitive: the
work-control prerequisite is accepted and pushed; the request-control focused
spec has a fresh executed PASS 9/9; and the UTF-8 focused spec has a fresh
executed PASS 7/7. The accepted SHA workspace optimization has 4,097-byte
full-versus-bounded parity and a cycle-3 bounded guard-probe PASS at 1.26 s and
43,852 KiB; the full qualified 1-MiB `W4-SRCH-31` oracle has not passed.
Consequently Wave 4S-C remains open: focused request-control, UTF-8, and bounded
SHA evidence does not close the SHA cell or prove the integrated production
pipeline.

The `cancel:true` gate requires an actual protocol 1.0 session test: transmit a
bounded long-running request, then a real framed canonical `cancel` operation
on the same byte stream, and observe cancellation before commit admission plus
a stable cancel response. A stepping/fake clock is useful unit evidence but can
never satisfy this transport/control-path gate.

## 11. Consequences

The design makes cancellation and deadlines falsifiable rather than cosmetic,
keeps memory bounded before typed admission, and removes whole-value copies
from the provider's scale-sensitive path. It also establishes reusable common
streaming JSON, SHA, Unicode, and process-stat boundaries for database/server
adapters.

The cost is explicit continuation state, segmented output, a reactor contract,
and chunk-partition parity testing. Protocol 1.0 cancel is still cooperative,
not preemptive: it is bounded only after the cancel frame traverses the ordered
transport and after the current work slice returns. That limitation is exposed
in negotiated limits and is accepted.

## 12. Active streaming-SHA performance blocker

`W4-SRCH-31` remains `FAIL`: fresh interpreter verification cycle 2 was
terminated at approximately 3:09 with zero output against a 180-second ceiling.
The accepted owner-local reusable 64-word schedule optimization has 4,097-byte
full-versus-bounded parity, and its cycle-3 bounded guard probe passed in 1.26 s
at 43,852 KiB. This is not the mandatory full qualified 1-MiB oracle and does
not close `W4-SRCH-31`. See
`doc/08_tracking/bug/spipe_streaming_sha_interpreter_value_array_copy_timeout_2026-08-25.md`.
