<!-- codex-design -->
# Parser Framework Detail Design

**Selection:** F2 + N2
**Architecture:** `doc/04_architecture/parser_framework.md`
**Status:** Frozen after independent API, layering, parallel, incremental, and QA review

## Ownership correction

The plan's `common/` path owns immutable cross-tier contracts, data records, and pure composition/hash helpers. Mutable runtime, sink, scalar/SIMD/GPU/incremental/auto executors land first in the required default tier `src/lib/nogc_async_mut/structural/parse/`. No parser execution mode uses the repo-root build-time `variants/` overlay.

## Frozen common contracts

Every named type below has one owner. `ArtifactId`, `StageReceipt`, and `MappingKind` are explicit imports from existing structural/placement owners; wildcard re-export is forbidden. `std.common.structural.identity.EntityRef` is the canonical compact structural reference; the compute-placement lane must explicitly alias/migrate its incompatible local `EntityRef` when both are imported.

```simple
# src/lib/common/structural/identity.spl
use std.common.compute.placement_contracts.storage.{ArtifactId}

struct EntityRef:
    object_slot: u32          # immutable arena-segment descriptor index
    local_index: u32          # element inside the segment

struct SnapshotId:
    root_artifact: ArtifactId
    epoch: i64

struct ScopedEntityRef:
    snapshot: SnapshotId
    entity: EntityRef

struct SourceSpan:
    byte_start: i64
    byte_end: i64

struct SourceAnchor:
    snapshot: SnapshotId
    span: SourceSpan
```

```simple
# src/lib/common/structural/parse/contracts.spl
use std.common.structural.execution.contracts.{StageReceipt}
use std.common.structural.mapping.contracts.{MappingKind}

val PARSE_CONTRACT_VERSION: i64 = 1

enum ParseErrorCode:
    InvalidDialect
    InvalidSnapshot
    InvalidEdit
    InvalidSpan
    MalformedUtf
    CountOverflow
    BackendWidthOverflow
    OutputUnderfill
    OutputOverfill
    StalePrior
    UnsupportedMode
    RequiredModeUnavailable
    ExecutorFailed

struct ParseError:
    code: ParseErrorCode
    message: text
    span: SourceSpan?

enum ParseExecutionMode:
    Scalar
    Simd
    Gpu
    Incremental
    Auto

enum FallbackPolicy:
    AllowScalar
    RequireRequested

enum TagDemand:
    Off
    Tags
    TagsAndIndexes

struct ParseOutputMask:
    tokens: bool
    syntax: bool
    tags: bool
    mappings: bool
    indexes: bool
    diagnostics: bool

struct TextEdit:
    base_span: SourceSpan      # coordinates in base_snapshot_id
    replacement: [u8]

class SourceSnapshot:
    id: SnapshotId
    parent_id: SnapshotId?
    bytes: [u8]
    newline_starts: [i64]

class ParseStringTable:
    byte_offsets: [i64]
    byte_lengths: [i64]
    bytes: [u8]

class TokenArena:
    kinds: [i64]
    byte_starts: [i64]
    byte_ends: [i64]
    value_ids: [i64]          # -1 means source-backed lexeme
    flags: [i64]

class SyntaxSegment:
    generation: u32
    source_base: i64
    source_digest: text
    entry_state_hash: text
    exit_state_hash: text
    grammar_rule: i64
    parent_fingerprint: text
    kinds: [i64]
    relative_starts: [i64]
    relative_ends: [i64]
    first_children: [i64]
    child_counts: [i64]
    children: [EntityRef]

class SyntaxArena:
    segments: [SyntaxSegment]
    roots: [EntityRef]

struct TagValue:
    kind: i64
    int_value: i64
    text_value_id: i64

struct TagRecord:
    node: EntityRef
    key: i64
    value: TagValue

class TagArena:
    records: [TagRecord]

struct ParseMapping:
    source: ScopedEntityRef
    target: ScopedEntityRef
    kind: MappingKind

class MappingArena:
    records: [ParseMapping]

struct QueryIndexKey:
    namespace_id: i64
    value_id: i64

struct QueryIndexRecord:
    key: QueryIndexKey
    node: EntityRef

class QueryIndexArena:
    records: [QueryIndexRecord]

struct DiagnosticRecord:
    code: text
    severity: i64
    span: SourceSpan
    message_id: i64
    local_ordinal: i64

class DiagnosticArena:
    records: [DiagnosticRecord]

struct ParseInvalidation:
    old_entity: ScopedEntityRef
    dependency_namespace: text
    dependency_key: text

class InvalidationSet:
    records: [ParseInvalidation]

class ParseResult:
    source: SourceSnapshot
    tokens: TokenArena
    syntax: SyntaxArena
    strings: ParseStringTable
    tags: TagArena
    mappings: MappingArena
    indexes: QueryIndexArena
    diagnostics: DiagnosticArena
    invalidation: InvalidationSet
    receipt: StageReceipt
```

All SoA column lengths are validated equal before exposure. Spans are half-open byte ranges within the snapshot. Newline starts are strictly ascending and start with zero. String IDs are `-1` or valid table rows. Segment references validate descriptor range and generation before access. Syntax spans are segment-relative, so unchanged segments may shift by changing only `source_base`.

## Frozen dialect and continuation contracts

```simple
# src/lib/common/structural/parse/dialect.spl
class LexContinuationState:
    mode: i64
    quote_kind: i64
    escape_run_parity: i64
    at_line_start: bool
    paren_depth: i64
    indent_stack: [i64]
    forced_indent_stack: [i64]
    pending_dedents: i64
    generic_close_depth: i64
    preprocessor_state: i64

class LexProgram:
    contract_version: i64
    state_count: i64
    start_state: i64
    max_gpu_states: i64
    opcodes: [i64]

class StructureProgram:
    contract_version: i64
    block_bytes: i64
    classification_mask: i64

class GrammarProgram:
    contract_version: i64
    entry_rules: [i64]
    production_offsets: [i64]
    opcodes: [i64]

class ActionProgram:
    contract_version: i64
    action_offsets: [i64]
    opcodes: [i64]

struct TagSchema:
    contract_version: i64
    key_ids: [i64]
    value_kinds: [i64]

struct MappingPolicy:
    emitted_kinds: [MappingKind]

struct IncrementalPolicy:
    checkpoint_bytes: i64
    max_stabilization_bytes: i64
    reusable_entry_rules: [i64]

class ParseDialect:
    dialect_id: text
    schema_version: i64
    lex: LexProgram
    structure: StructureProgram
    grammar: GrammarProgram
    actions: ActionProgram
    tags: TagSchema
    mapping: MappingPolicy
    incremental: IncrementalPolicy

fn validate_parse_dialect(dialect: ParseDialect) -> Result<(), ParseError>
```

The current handwritten Simple grammar remains the sole grammar during Wave 1a and is instrumented to emit through the new sink. Wave 1b mechanically extracts its rules/actions into `GrammarProgram`/`ActionProgram`, routes both `ParseRuntime` and the legacy wrapper to those tables, and removes the old rule bodies in the same cutover. Completion does not permit two live Simple grammars.

## Frozen output reservation and sink API

```simple
# src/lib/common/structural/parse/output_plan.spl
struct OutputRange:
    start: i64
    count: i64

struct ParseOutputCounts:
    tokens: i64
    nodes: i64
    children: i64
    tags: i64
    mappings: i64
    indexes: i64
    diagnostics: i64

struct ParseOutputRanges:
    tokens: OutputRange
    nodes: OutputRange
    children: OutputRange
    tags: OutputRange
    mappings: OutputRange
    indexes: OutputRange
    diagnostics: OutputRange

fn checked_output_ranges(counts: ParseOutputCounts, backend_max: i64) -> Result<ParseOutputRanges, ParseError>

# src/lib/nogc_async_mut/structural/parse/action_sink.spl
class ParseActionSink:
    source: SourceSnapshot
    result: ParseResult
    ranges_reserved: bool
    write_counts: ParseOutputCounts

impl ParseActionSink:
    me reserve_outputs(counts: ParseOutputCounts, backend_max: i64) -> Result<ParseOutputRanges, ParseError>
    me emit_token_at(range: OutputRange, ordinal: i64, kind: i64, span: SourceSpan, value_id: i64, flags: i64) -> Result<(), ParseError>
    me emit_node_at(range: OutputRange, ordinal: i64, kind: i64, span: SourceSpan, children: [EntityRef]) -> Result<EntityRef, ParseError>
    me emit_tag_at(range: OutputRange, ordinal: i64, record: TagRecord) -> Result<(), ParseError>
    me emit_mapping_at(range: OutputRange, ordinal: i64, record: ParseMapping) -> Result<(), ParseError>
    me emit_index_at(range: OutputRange, ordinal: i64, record: QueryIndexRecord) -> Result<(), ParseError>
    me emit_diagnostic_at(range: OutputRange, ordinal: i64, record: DiagnosticRecord) -> Result<(), ParseError>
    me finish() -> Result<ParseResult, ParseError>
```

Reservation happens once after every count/scan succeeds. Each write must land exactly in `[range.start, range.start + range.count)`; duplicate, underfill, and overfill are errors. `finish` validates every reserved slot, SoA length, span, reference, demand rule, and deterministic ordering. `TagDemand.Off` forces tag/index counts to zero and never allocates their arrays.

## Runtime, mode, and evidence contracts

```simple
# src/lib/nogc_async_mut/structural/parse/runtime.spl
class ParseThresholds:
    evidence_digest: text
    minimum_speedup_milli: i64

class ParseExecutionProfile:
    mode: ParseExecutionMode
    fallback: FallbackPolicy
    thresholds: ParseThresholds

class ParseRequest:
    source: SourceSnapshot              # final bytes after edits
    base_snapshot_id: SnapshotId?
    prior: ParseResult?
    edits: [TextEdit]                   # coordinates in base_snapshot_id
    entry_rule: i64
    outputs: ParseOutputMask
    tag_demand: TagDemand
    execution: ParseExecutionProfile

class ParseRuntime:
    dialect: ParseDialect
    runtime_version: i64

struct ParseBenchmarkEvidence:
    dialect_id: text
    schema_version: i64
    runtime_version: i64
    backend: text
    device_driver_identity: text
    binary_revision: text
    source_revision: text
    fixture_id: text
    size_class: text
    stage: text
    output_mask: ParseOutputMask
    tag_demand: TagDemand
    warm: bool
    scalar_median_us: i64
    optimized_median_us: i64
    p95_us: i64
    max_rss_bytes: i64
    allocation_count: i64
    parity: bool
    evidence_digest: text

struct ParseModeDecision:
    requested: ParseExecutionMode
    selected: ParseExecutionMode
    fallback_reason: text
    evidence_digest: text

fn parse_runtime(dialect: ParseDialect) -> Result<ParseRuntime, ParseError>
fn parse_request(runtime: ParseRuntime, request: ParseRequest) -> Result<ParseResult, ParseError>
fn parse_result_fingerprint(result: ParseResult) -> text
fn parse_results_equal(left: ParseResult, right: ParseResult) -> bool
fn select_parse_mode(runtime: ParseRuntime, request: ParseRequest, evidence: [ParseBenchmarkEvidence]) -> ParseModeDecision
```

`parse_result_fingerprint` includes semantic arrays and deterministic receipt fields (`input_hash`, `output_hash`, item/byte counts, malformed/overflow flags, `deterministic_hash`). It excludes backend, mode, fallback provenance, elapsed/cpu/gpu telemetry, and layout-only receipt fields. `parse_results_equal` first checks non-empty absolute oracle facts for the fixture, then semantic equality; self-comparison is not evidence.

## Structural index and parallel lexical contracts

```simple
struct StructuralBlockState:
    entry: LexContinuationState
    exit: LexContinuationState
    digest: text

class StructuralIndex:
    positions: [i64]
    kinds: [i64]
    blocks: [StructuralBlockState]

class LexChunkSummary:
    source_span: SourceSpan
    source_digest: text
    state_count: i64
    next_states: [i64]
    token_counts: [i64]
    diagnostic_counts: [i64]
    region_counts: [i64]
    malformed_flags: [i64]
    overflow_flags: [i64]

struct LexChunkState:
    entry_state: i64
    exit_state: i64

class ParallelLexPlan:
    summaries: [LexChunkSummary]
    states: [LexChunkState]
    token_ranges: [OutputRange]
    diagnostic_ranges: [OutputRange]
    region_ordinals: [i64]

class ParallelLexOutput:
    tokens: TokenArena
    diagnostics: DiagnosticArena
    region_ordinals: [i64]

fn build_structural_index(dialect: ParseDialect, snapshot: SourceSnapshot) -> Result<StructuralIndex, ParseError>
fn compose_chunk_summaries(program: LexProgram, summaries: [LexChunkSummary]) -> Result<[LexChunkState], ParseError>
fn emit_parallel_tokens(dialect: ParseDialect, plan: ParallelLexPlan) -> Result<ParallelLexOutput, ParseError>
```

A summary is a total table for every admitted entry state. Identity maps each state to itself with zero counts. Ordered composition is `(A then B).next[s] = B.next[A.next[s]]`; each count is `checked_add(A.count[s], B.count[A.next[s]])`. Table lengths/state IDs, nonnegative counts, host/backend widths, `count * element_size`, and all exclusive scans validate before allocation or dispatch. Emitters fill exact disjoint ranges. Regions receive a unique source-sorted ordinal using `(byte_start, byte_end, kind_priority, discovery_ordinal)` before worker execution; only that ordinal controls commit.

Admission validates device/driver, input/chunk limits, state cardinality, nesting, region placement, backend index/buffer limits, output mask, `TagDemand`, evidence identity/parity, and N2 speedup. Backend-width-only overflow is an optimized-mode fallback before dispatch; canonical host count overflow is always fatal. Execution uses a private staging output; `AllowScalar` discards it and records exactly one stable reason, while `RequireRequested` returns `RequiredModeUnavailable` and never runs scalar.

## Incremental contract and algorithm

```simple
class IncrementalParsePlan:
    base_snapshot_id: SnapshotId
    stabilized_spans: [SourceSpan]
    reused_segment_slots: [u32]
    reparsed_region_ordinals: [i64]

fn incremental_parse_plan(runtime: ParseRuntime, request: ParseRequest) -> Result<IncrementalParsePlan, ParseError>
```

`request.source` is the final snapshot. `base_snapshot_id`, `prior.source.id`, and every edit coordinate agree; applying normalized non-overlapping edits to prior bytes must produce the final artifact digest. Stabilization starts at a checkpoint and ends only at a mapped unchanged boundary where chunk digest plus the complete entry/exit `LexContinuationState` match. Preprocessor edits, unavailable checkpoints, or the policy byte cap fall back to full parse.

Segments use relative spans. Reuse requires region digest, full lexical entry/exit hashes, entry rule, parent fingerprint, schema version, and valid generation; whole-source digest is not required. Retained mappings use `ScopedEntityRef` on both revisions. Replaced old entities and namespaced dependency keys populate invalidation. Current global compiler pools are never retained; the adapter copies once into owned segments until those pools are removed.

## Simple compatibility cutover

The existing parser scans character indices while canonical spans are bytes. Wave 0 tracks byte offsets beside current scan positions and validates non-ASCII UTF fixtures. `legacy_bridge.spl` alone derives compiler `Span` line/column/character presentation. Wave 1a instruments the existing parser to emit owned results before `ast_reset`. Wave 1b extracts/deletes the old grammar bodies atomically. SIMD, GPU, incremental, and auto modes cannot promote before the new scalar result matches the legacy normalized oracle.

## Scalar and optimized flow

<!-- sdn-diagram:id=parser_framework.sequence -->
<details class="sdn-source"><summary>SDN source</summary>

```sdn id=parser_framework.sequence hash=sha256:auto render=ascii
@layout dag
@direction LR

ParseRequest -> ValidateDialectSnapshotEdits
ValidateDialectSnapshotEdits -> SelectMode
SelectMode -> CountAndScan
CountAndScan -> PrivateExecutorOutput
PrivateExecutorOutput -> OrderedSinkCommit
OrderedSinkCommit -> ValidateAbsoluteOracle
ValidateAbsoluteOracle -> SemanticHash
SemanticHash -> ParseResult
PrivateExecutorOutput -x PublicPartialOutput
```

</details>
<details class="sdn-ascii" open><summary>Diagram</summary>

```ascii generated-from=parser_framework.sequence hash=sha256:auto
request -> validate -> select -> count/scan -> private output -> ordered sink -> oracle/hash -> result
                                               |
                                               x no public partial output
```

</details>
<!-- sdn-diagram:end -->

## N2 evidence protocol

The canonical fixture manifest and immutable pre-change baseline identify exact source/binary revisions. Retained rows include host/device/driver, stage, output mask/demand, warm/cold, sample count, median, p95, max RSS, allocation counters, crossover decision, parity, and evidence digest. GPU end-to-end boundaries include upload, launch, synchronization, readback, ordered materialization, and hash; device-only time is separate. Promotion requires matching identity, parity, and `scalar_median / optimized_median >= 1.5`. Scalar median must remain within 1.10× oracle; ≤1% edit median must be ≤0.25× full parse; RSS must be ≤0.50× baseline and return after released stages.

## Explicit exports

Each common module exports only its named types/functions. `src/lib/nogc_async_mut/structural/parse/__init__.spl` explicitly re-exports the public common contracts and default runtime entrypoints; it is not a wildcard hub. No raw `rt_*`, environment read, filesystem scan, subprocess, backend-field poke, or request-time threshold load is permitted.
