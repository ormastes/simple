# Simple GPU Frontend Offload and Unified Parser Architecture & Implementation Plan

**Date:** 2026-09-01  
**Repository baseline:** [`ormastes/simple@1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae`](https://github.com/ormastes/simple/tree/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae)  
**Status:** Proposed architecture and staged refactoring plan  
**Extends:** [Parser Framework Detail Design](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/doc/05_design/parser_framework.md), [Simple Compiler Offload Detail Design](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/doc/05_design/simple_compiler_offload.md), and the 2026-07-31 tagged structural-compute architecture  
**Primary decision:** Offload the complete valid-source frontend to SIMD/GPU except **global name resolution** and **syntax error recovery**. Preserve the original full CPU frontend permanently as an independently implemented oracle and emergency production path.

---

## Executive decision

Simple should use one parser platform with several execution backends and several language dialects. The platform owns source normalization, UTF validation, lexical-state composition, structural indexing, tokenization, region mapping, grammar execution, direct Parsed HIR emission, tags, source-to-IR mappings, incremental reuse, and cache identity. It must not duplicate these mechanisms in the compiler, interpreter, shell, SDN, or a misleading “TreeSitterParser” implementation.

The target valid-source path is:

```text
input encoding
  -> canonical UTF-8 + original-to-UTF-8 source map
  -> UTF-8 validation and byte classification
  -> string/comment/raw masks
  -> delimiter, indentation, token, function, statement, and expression maps
  -> region work table
  -> GPU/local parser
  -> Parsed HIR + local bindings + type constraints
  -> CPU global-name binding
  -> GPU semantic/type continuation
  -> Typed HIR / downstream compiler
```

The CPU remains first class through two distinct paths:

1. **Legacy full CPU frontend:** the current compiler lexer/parser, AST pools, desugaring, and lowering path. It remains available, buildable without a GPU, independently tested, and callable with an explicit override. It is never silently replaced by GPU output.
2. **Canonical CPU runtime:** scalar and SIMD executors run the same generated `LexProgram`, `StructureProgram`, `RegionProgram`, `GrammarProgram`, and `ActionProgram` used by the GPU. This is the normal per-region fallback and the portable production implementation.

The two CPU paths serve different purposes. The canonical CPU runtime prevents grammar/backend drift. The legacy full CPU frontend preserves implementation diversity and catches common-mode defects in the generated runtime.

The GPU does not attempt syntax repair or cross-module/global name binding. These are explicit CPU stages, not “GPU failures.” Other unsupported or failed units are placed in a compact CPU work queue with stable tags, reasons, handler IDs, input mappings, output-count slots, and deterministic commit ordinals.

The parser-unification rule is:

> **Share one parser runtime and one cache protocol, not one semantic grammar.**

`SimpleDialect`, `SdnDialect`, and `SoshDialect` have different grammar/action programs but use the same source, UTF, token, region, work, mapping, execution, and cache contracts. Native Tree-sitter uses its own runtime, but its Simple grammar is generated from the same canonical Simple grammar source and carries the same grammar digest and conformance corpus.

---

## 1. Goals, scope, and non-goals

### 1.1 Goals

This plan delivers:

- GPU execution for encoding conversion, UTF-8 validation/classification, lexical-state masks, structural indexing, tokenization, region mapping, valid-source parsing, direct Parsed HIR emission, local scope/name binding, type-constraint generation, and post-global-binding semantic/type work.
- CPU-only ownership of global name resolution and syntax error recovery.
- Per-region CPU processing for known-hard or pre-emission failed GPU work, with explicit `CPU_TODO`, `HARD`, `FAIL`, `RECOVERY`, and `GLOBAL_NAME` tags.
- A permanent original full CPU parser path and a canonical scalar/SIMD runtime.
- One generated canonical Simple grammar with mechanically derived compiler tables, Tree-sitter grammar, token IDs, precedence tables, capability maps, and conformance tests.
- Parser-platform reuse by the Simple compiler, Simple interpreter/REPL, Simple shell/sosh, and SDN.
- A truthful native/Wasm Tree-sitter integration for editor/incremental/error-tolerant CST use.
- A homogenized, content-addressed cache hierarchy shared across parser consumers and execution backends.
- Non-breaking migration with adapters at every boundary.
- Deterministic output, exact stage receipts, differential verification, and evidence-gated performance promotion.

### 1.2 Non-goals

This plan does not:

- Make Tree-sitter the semantic authority for the compiler.
- Force Simple, sosh, and SDN to use the same grammar.
- Remove the current full CPU parser.
- Claim that “one-pass language” means one literal kernel or one memory read. It means source does not require later semantic reinterpretation; the implementation may use several parallel count/scan/emit stages.
- Use GPU execution for tiny interactive requests when measured transfer, launch, or synchronization cost is worse than scalar/SIMD CPU execution.
- Treat malformed source as a normal GPU grammar case. GPU stages may identify malformed spans, but CPU recovery owns repair decisions and final recovery diagnostics.
- Use heuristic source-encoding detection. Encoding is selected by explicit configuration, BOM, or the project default of UTF-8.
- Introduce pointer-rich GPU AST objects. The production path emits flat syntax sidecars and Parsed HIR directly.

---

## 2. Current repository audit

The audit below is based on the pinned repository baseline, not only earlier plans.

| Area | Current implementation truth | Decision |
|---|---|---|
| Compiler parser | [`src/compiler/10.frontend/core/parser.spl`](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/src/compiler/10.frontend/core/parser.spl) is a large module-global recursive-descent frontend that writes compiler AST arenas and coordinates several split parser modules. | Preserve under a stable legacy CPU facade; make it reentrant/session-scoped where practical; instrument it as a normalized oracle. |
| Shared compiler/interpreter core entry | [`src/compiler/10.frontend/core/frontend.spl`](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/src/compiler/10.frontend/core/frontend.spl) already centralizes parse/reset/append/isolated entrypoints and post-parse interpolation transforms. | Reuse as the first integration seam; replace its direct parser call with a selectable frontend provider. |
| Current HIR path | [`src/compiler/10.frontend/core/hir/lowering.spl`](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/src/compiler/10.frontend/core/hir/lowering.spl) exposes a separate AST-to-HIR lowering path rather than a complete direct-HIR parser sink. | Keep as the legacy adapter/oracle; add `ParsedHirSink` and migrate consumers incrementally. |
| Existing frontend cache | [`frontend_parse_cache.spl`](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/src/compiler/10.frontend/frontend_parse_cache.spl) caches/restores flat parser pools for unchanged modules. | Retain as a compatibility payload; place it behind the new content-addressed cache API and migrate to region/Parsed-HIR artifacts. |
| Parser framework Wave 1 | [`parse_types.spl`](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/src/lib/common/structural/parse/parse_types.spl) and [`parse_cpu_reference.spl`](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/src/lib/common/structural/parse/parse_cpu_reference.spl) implement a flat-byte, span-token, lexical DFA CPU oracle with explicit capacity rejection and fallback receipts. | Preserve as v1 compatibility and reuse its fail-closed principles, but do not mistake it for a full Simple parser. |
| Structural indexing | [`structural_index.spl`](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/src/lib/nogc_async_mut/structural/parse/structural_index.spl) is an explicit Wave-1 unsupported-mode stub. | Implement in v2 using shared scalar/SIMD/GPU contracts. |
| Parallel lexing | [`parallel_lex.spl`](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/src/lib/nogc_async_mut/structural/parse/parallel_lex.spl) defines summary/plan records but its composition and emission functions are unsupported-mode stubs. | Implement chunk-function composition, count/scan/emit, and exact range validation. |
| Incremental parsing | [`incremental.spl`](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/src/lib/nogc_async_mut/structural/parse/incremental.spl) is a Wave-1 stub. | Implement only after region identity and entry/exit state hashes are stable. |
| Auto dispatch | [`auto_profile.spl`](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/src/lib/nogc_async_mut/structural/parse/auto_profile.spl) always selects scalar and records that the profile is unimplemented. | Replace with evidence- and residency-aware per-stage dispatch. |
| Action sink | [`action_sink.spl`](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/src/lib/nogc_async_mut/structural/parse/action_sink.spl) currently re-exports immutable push-style helpers; [`output_plan.spl`](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/src/lib/common/structural/parse/output_plan.spl) defines checked ranges but is not wired to a full parser. | Replace hot-path push growth with two-pass exact reservation and disjoint indexed writes. |
| Parser framework tests | [`parse_cpu_reference_spec.spl`](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/test/01_unit/lib/structural/parse/parse_cpu_reference_spec.spl) and [`parser_framework_spec.spl`](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/test/03_system/app/compiler/feature/parser_framework_spec.spl) verify a toy four-state lexical DFA and explicit accelerated-mode demotion. | Keep them, then add real Simple/SDN/sosh grammars, structure, HIR, incremental, and forced-backend tests. |
| Interpreter parsers | [`src/app/interpreter/parser.spl`](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/src/app/interpreter/parser.spl) wraps a “TreeSitterParser”; [`parser_pure.spl`](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/src/app/interpreter/parser_pure.spl) wraps another simplified parser. | Replace both with entry-rule adapters over `SimpleDialect`; preserve temporary compatibility wrappers only. |
| Simplified common parser | [`src/lib/common/parser/parser.spl`](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/src/lib/common/parser/parser.spl) contains a second, simplified Simple grammar. | Stop treating it as an independent grammar; adapt it to `ParseRuntime`, then delete old rule bodies after parity. |
| Current “TreeSitterParser” | [`src/compiler_rust/lib/std/src/parser/treesitter/__init__.spl`](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/src/compiler_rust/lib/std/src/parser/treesitter/__init__.spl) contains its own reduced token set, scalar lexer, arena, and minimal parser. The repository audit found no generated Simple `grammar.js`/`grammar.json`/`parser.c` in this path. | Rename it so it is not labeled native Tree-sitter; add a generated native/Wasm Tree-sitter provider from the canonical grammar. |
| sosh command/pipeline parsing | [`commands_fs.spl`](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/src/os/apps/shell/_ShellApp/commands_fs.spl), [`shell_pipe.spl`](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/src/os/apps/shell/shell_pipe.spl), [`shell_redirect.spl`](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/src/os/apps/shell/shell_redirect.spl), and [`shell_script.spl`](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/src/os/apps/shell/shell_script.spl) repeat quote, escape, split, redirect, and block-depth logic. | Replace with `SoshDialect` entry rules and a `ShellHirSink`; keep execution/expansion separate from parsing. |
| SDN | [`src/lib/common/sdn/lexer.spl`](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/src/lib/common/sdn/lexer.spl) defines a small lexer, while [`parser.spl`](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/src/lib/common/sdn/parser.spl) also scans source text directly for delimiters, quotes, indentation, and separators. | Implement `SdnDialect`; retain the current parser as its CPU oracle until differential parity, then route public APIs through the shared runtime. |
| Text SIMD | Existing UTF/text design and optimization documents establish byte-oriented UTF-8, runtime SIMD dispatch, and source-backed spans. | Reuse those primitives, but explicitly implement parser-specific fused classification, structure, token, and region stages; the parser SIMD backend is not currently complete. |

### 2.1 Contract inconsistencies that must be corrected first

The current parser-framework scaffolding has several intentional Wave-1 compatibility seams that cannot be carried into GPU execution unchanged:

1. `contracts.spl` defines an enum-style `ParseExecutionMode`, while `parse_types.spl` also exposes string modes such as `cpu_reference`, `hybrid_vector_gpu`, and `resident_gpu`. v2 must have one canonical typed representation and text serialization only at CLI/config boundaries.
2. `dialect.spl` declares richer future `LexProgram`, `StructureProgram`, `GrammarProgram`, and `ActionProgram` classes but aliases `ParseDialect` to the lexical-only legacy dialect. v2 must make the rich bundle real.
3. `model.spl` is a facade that re-exports Wave-1 lexical types. v2 must own syntax, region, work, HIR, mapping, and invalidation records rather than only re-exporting placeholders.
4. The current CPU-reference fingerprint hashes token kinds/spans and diagnostics but leaves `StageReceipt.input_hash` empty. The tests intentionally show that different lexeme bytes with the same token shape can share a hash. This is sufficient for the current toy lexical test but insufficient for semantic parity or cache identity.
5. `parse_source_blob_from_text` copies bytes through repeated `push`. The canonical source representation must support borrowed/owned immutable bytes and avoid a mandatory extra copy.
6. Push-style sinks cannot provide exact disjoint GPU write ranges. Count/scan/reserve/emit/finish must be the only accelerated-path allocation protocol.
7. Current structural, parallel-lex, incremental, and auto-dispatch APIs are stubs. Mode labels must never imply acceleration until the corresponding executor actually ran.

### 2.2 Current grammar-divergence risks

The repo currently has multiple live representations of “Simple parsing”:

- the full compiler parser;
- the simplified common parser;
- the reduced Simple-coded “TreeSitterParser”;
- interpreter wrappers choosing between those paths;
- separate token/grammar knowledge in editor/tooling code;
- line-oriented preprocessing and custom-block extraction ahead of the compiler parser.

This is already semantic divergence, even before GPU code exists. Specific lexical hazards include:

- `//` is a Simple parallel/composition operator, not a universal line-comment marker;
- `#` participates in comments and token/attribute/hash contexts;
- `'` can be a quoted delimiter and a context-specific transpose operator;
- raw strings, triple strings, interpolation, indentation, `<<< >>>`, and custom blocks require lexical modes;
- custom blocks such as `m{}`, `loss{}`, `sh{}`, `sql{}`, and collection literals reuse braces but have different payload/action semantics.

A GPU lexer must derive these rules from the same canonical lexical specification as every CPU and tooling parser. Hand-maintained parallel token lists are prohibited after the grammar cutover.

---

## 3. Architecture invariants

These invariants are release-blocking rules.

1. **One immutable source snapshot.** Hashing, normalization, parsing, diagnostics, incremental edits, Tree-sitter sessions, and caches read one `SourceSnapshot`; consumers do not reopen or independently decode the file.
2. **Canonical valid UTF-8 internally.** Source may be explicitly decoded from UTF-16/32 or a supported legacy codec at the I/O boundary, but all parser spans are UTF-8 byte ranges.
3. **Source-backed lexemes.** Tokens carry `(byte_start, byte_count)` and optional interned value IDs; they do not own copied token text by default.
4. **One generated Simple grammar.** Compiler, canonical scalar/SIMD/GPU runtime, interpreter, and Tree-sitter projection all identify the same grammar digest.
5. **Shared representation across backends.** Scalar, SIMD, and GPU executors consume and emit the same flat contracts. Backend-specific layouts may exist only behind validated conversion/view adapters.
6. **Original CPU frontend never deleted.** It remains runnable without GPU libraries and participates in differential release tests.
7. **No silent fallback.** Every backend demotion, hard task, failed task, recovery task, or global-name task has a reason code and receipt.
8. **No partial trusted output after late execution failure.** Output is built in private staging storage and committed only after exact count, range, reference, and hash validation.
9. **Deterministic source order.** Region ordinals and output ranges, not worker completion order or atomics, determine observable order.
10. **Global names and recovery are CPU-owned.** This is an architecture boundary, not a temporary GPU TODO.
11. **Valid-source GPU path emits Parsed HIR directly.** A full AST is optional tooling output, not a required compiler intermediate.
12. **Sidecars, not wider nodes.** Tags, mappings, indexes, provenance, work status, and receipts remain sidecar arenas compatible with MDSOC+.
13. **Backend-independent semantic cache keys.** Once parity is certified, identical scalar/SIMD/GPU semantic outputs share cache identity; execution provenance remains in receipts.
14. **Small work stays CPU/SIMD when faster.** Auto mode includes transfer, queue, launch, synchronization, and readback costs.
15. **Capabilities are generated and auditable.** Every grammar opcode/action declares scalar, SIMD, GPU, recovery, and legacy-handler support.

---

## 4. Execution model

### 4.1 Keep existing top-level offload modes

Do not multiply public build variants. Preserve the existing offload profile concepts:

| Mode | Meaning |
|---|---|
| `cpu_reference` | Canonical scalar runtime by default; explicit `legacy_cpu_full` override remains available. No GPU initialization. |
| `hybrid_vector_gpu` | Per-stage and per-region choice among scalar, SIMD, GPU, and CPU task drain. Source/IR may move between host and device. |
| `resident_gpu` | UTF indexes, tokens, regions, work tables, Parsed HIR, and eligible semantic tables remain in device/Object-VM storage; CPU exchanges only compact task/name/recovery tables and patches. |
| `auto` | Evidence-based selection using exact workload, device, residency, output mask, and cache state. |

`verify_dual` is an assurance policy, not another execution mode. It runs the selected backend and one or both CPU oracles, then compares normalized artifacts.

### 4.2 Explicit frontend provider identity

The execution backend and parser provider are different dimensions:

```simple
# Conceptual contract
enum ParserProvider:
    SimpleLegacyCpu
    SimpleCanonical
    NativeTreeSitter
    WasmTreeSitter
    FallbackLine
    FallbackBinary

enum ParseBackend:
    ScalarCpu
    SimdCpu
    Gpu
```

A Simple-coded fallback must not report itself as native Tree-sitter. Cache and diagnostic provenance must preserve the provider identity exactly.

### 4.3 Fallback policy

```simple
enum FrontendFallbackPolicy:
    AllowRegionCpu       # known-hard/recovery regions use canonical CPU
    AllowFullCpu         # late stage/device failure may rerun private stage on CPU
    RequireRequested     # no demotion; return an error
```

Recommended defaults:

- development: `AllowFullCpu + verify_dual`;
- ordinary production: `AllowRegionCpu`, with late device failure allowed to rerun the affected private stage on CPU;
- mission-critical/reproducibility lane: explicit profile, forced backend, CPU oracle sampling or full dual execution;
- performance benchmark lane: `RequireRequested`, so fallback cannot inflate apparent GPU success.

---

## 5. Canonical frontend data model

The existing parser framework should move to a versioned v2 contract rather than silently widening Wave 1.

### 5.1 Source and normalization

```simple
struct SourceSnapshot:
    id: SnapshotId
    raw_artifact: ArtifactId
    normalized_artifact: ArtifactId
    parent: SnapshotId?
    encoding: SourceEncoding
    utf8: ByteView
    newline_starts: ObjectRef<U64Arena>
    normalization_map: ObjectRef<SourceOffsetMap>
    content_digest: Hash256

struct SourceOffsetCheckpoint:
    original_byte: u64
    utf8_byte: u64

struct SourceOffsetMap:
    checkpoints: ObjectRef<SourceOffsetCheckpointArena>
    checkpoint_stride: u32
```

The offset map uses block checkpoints plus local decoding rather than a mapping entry per scalar. UTF-8 input can use an identity map.

### 5.2 Classification and structural tables

```simple
struct UtfClassBlock:
    byte_base: u64
    ascii_mask: u64
    continuation_mask: u64
    non_ascii_lead_mask: u64
    whitespace_mask: u64
    newline_mask: u64
    quote_mask: u64
    apostrophe_mask: u64
    slash_mask: u64
    hash_mask: u64
    backslash_mask: u64
    lparen_mask: u64
    rparen_mask: u64
    lbracket_mask: u64
    rbracket_mask: u64
    lbrace_mask: u64
    rbrace_mask: u64
    less_mask: u64
    greater_mask: u64
    invalid_mask: u64

struct LexStateBlock:
    byte_start: u64
    byte_end: u64
    entry_state: u32
    exit_state: u32
    opaque_mask_ref: ObjectRef<BitBlockArena>
    digest: Hash256

struct DelimiterPair:
    open_byte: u64
    close_byte: u64
    kind: DelimiterKind
    parent_pair: u32
    depth: u32
    flags: u32

struct IndentLine:
    line_index: u32
    first_code_byte: u64
    column: u32
    parent_line: u32
    block_end_line: u32
    flags: u32
```

Candidate delimiter bits are produced during UTF classification; final structural delimiters are produced only after opaque string/comment/raw masks are known.

### 5.3 Tokens and regions

```simple
struct TokenArena:
    kind: [u16]
    byte_start: [u64]
    byte_count: [u32]
    value_id: [u32]       # NO_ID means source-backed
    flags: [u32]

struct RegionTable:
    kind_hint: [u16]
    byte_start: [u64]
    byte_end: [u64]
    token_start: [u32]
    token_count: [u32]
    parent_region: [u32]
    first_child_region: [u32]
    child_region_count: [u32]
    entry_rule: [u32]
    entry_state_hash: [Hash128]
    exit_state_hash: [Hash128]
    stable_ordinal: [u32]
    flags: [u32]
```

`RegionTable` is deliberately a **map, not parsed syntax**. It says that a range is likely a file, declaration, function header, body, statement, expression, parameter list, or embedded block. The grammar executor still validates and parses the region.

### 5.4 Parsed HIR and semantic sidecars

```simple
struct ParsedHirArena:
    kind: [u16]
    source_region: [u32]
    byte_start: [u64]
    byte_end: [u64]
    first_child: [u32]
    child_count: [u32]
    first_operand: [u32]
    operand_count: [u32]
    name_key: [u32]
    local_symbol: [u32]
    type_var: [u32]
    flags: [u32]

struct NameOccurrenceTable:
    name_key: [u32]
    scope_id: [u32]
    hir_node: [u32]
    occurrence_kind: [u16]
    candidate_start: [u32]
    candidate_count: [u32]
    flags: [u32]

struct TypeConstraintArena:
    lhs_type_var: [u32]
    relation: [u16]
    rhs_kind: [u16]
    rhs_value: [u32]
    source_hir: [u32]
```

`ParsedHirArena` may contain unresolved global `name_key` values. Local declarations and local references should already carry stable local IDs when the region/scope structure permits it.

---

## 6. End-to-end frontend pipeline

```text
┌───────────────────────────────────────────────────────────────────────────┐
│ 0. ParserSession + cache lookup                                           │
│    source identity, dialect/grammar identity, edits, output demand        │
└──────────────────────────────────┬────────────────────────────────────────┘
                                   ▼
┌───────────────────────────────────────────────────────────────────────────┐
│ 1. Decode/transcode to canonical UTF-8                                    │
│    explicit encoding/BOM -> normalized bytes + source offset checkpoints  │
└──────────────────────────────────┬────────────────────────────────────────┘
                                   ▼
┌───────────────────────────────────────────────────────────────────────────┐
│ 2. UTF-8 validate + classify                                              │
│    lead/continuation validity, whitespace/newline, delimiter candidates   │
└──────────────────────────────────┬────────────────────────────────────────┘
                                   ▼
┌───────────────────────────────────────────────────────────────────────────┐
│ 3. Compose lexical continuation states                                   │
│    strings, raw/triple strings, comments, escapes, interpolation, payload │
│    -> opaque masks                                                        │
└──────────────────────────────────┬────────────────────────────────────────┘
                                   ▼
┌───────────────────────────────────────────────────────────────────────────┐
│ 4. Structural filtering and pairing                                      │
│    () [] {} <<< >>>, line boundaries, indentation parents/ends            │
└──────────────────────────────────┬────────────────────────────────────────┘
                                   ▼
┌───────────────────────────────────────────────────────────────────────────┐
│ 5. Token boundary/kind-hint generation and compaction                     │
│    ASCII fast path; Unicode XID lookup only for non-ASCII scalar starts   │
└──────────────────────────────────┬────────────────────────────────────────┘
                                   ▼
┌───────────────────────────────────────────────────────────────────────────┐
│ 6. Region skeleton map                                                    │
│    file/type/function/header/body/statement/expression/custom block       │
└──────────────────────────────────┬────────────────────────────────────────┘
                                   ▼
┌───────────────────────────────────────────────────────────────────────────┐
│ 7. Work admission + GPU/CPU count                                         │
│    capability map -> HARD/RECOVERY/GLOBAL_NAME tags; count output records │
└──────────────────────────────────┬────────────────────────────────────────┘
                                   ▼
┌───────────────────────────────────────────────────────────────────────────┐
│ 8. Stable global output scan/reservation                                  │
│    merge GPU counts + CPU-todo counts in region order                     │
└──────────────────────────────────┬────────────────────────────────────────┘
                                   ▼
┌───────────────────────────────────────────────────────────────────────────┐
│ 9. GPU and CPU region emission                                            │
│    syntax-on-demand, Parsed HIR, local names, constraints, tags, mappings │
└──────────────────────────────────┬────────────────────────────────────────┘
                                   ▼
┌───────────────────────────────────────────────────────────────────────────┐
│ 10. Validate and ordered commit                                           │
│     exact fill, references, digests, deterministic order, private staging │
└──────────────────────────────────┬────────────────────────────────────────┘
                                   ▼
┌───────────────────────────────────────────────────────────────────────────┐
│ 11. CPU global name resolution                                            │
│     imports/modules/exports/overload candidate sets -> GlobalBindingTable │
└──────────────────────────────────┬────────────────────────────────────────┘
                                   ▼
┌───────────────────────────────────────────────────────────────────────────┐
│ 12. GPU semantic/type continuation                                       │
│     apply global bindings, solve eligible constraints, emit Typed HIR     │
└──────────────────────────────────┬────────────────────────────────────────┘
                                   ▼
┌───────────────────────────────────────────────────────────────────────────┐
│ 13. Consumer projection + layered cache publish                           │
│     compiler/interpreter/CST/shell/SDN output, receipts, invalidation     │
└───────────────────────────────────────────────────────────────────────────┘
```

Stages 2–5 should be fused selectively, but each logical output remains independently testable and cacheable. A fused kernel is an optimization, not a different semantic implementation.

---

## 7. Encoding, UTF-8 validation, and early block tagging

### 7.1 Encoding selection

Precedence:

1. explicit compiler/API request;
2. BOM where the selected policy permits BOMs;
3. project/source policy;
4. UTF-8 default.

Do not guess from byte frequency. A guessed codec can make identifiers, delimiters, and source mappings non-deterministic.

### 7.2 CPU versus GPU conversion

- Tiny and isolated files: scalar or existing CPU SIMD transcoder.
- Medium files: CPU SIMD unless data is already device-resident or GPU batching amortizes launch/transfer.
- Large batches, large generated source, or resident compilation: GPU transcode and classify.
- UTF-8 input: validate and classify directly; do not transcode through UTF-32.
- UTF-16/32 input: count UTF-8 output bytes, scan output offsets, emit UTF-8, and build offset checkpoints.

The CPU implementation should reuse the runtime-dispatch model demonstrated by [simdutf](https://github.com/simdutf/simdutf), which provides validation/transcoding implementations selected for the running processor. GPU conversion must match the canonical scalar codec exactly, including malformed-input positions.

### 7.3 UTF validation can tag candidate block bytes

The validation/classification pass should emit dense masks for:

- UTF-8 lead/continuation validity;
- ASCII/non-ASCII;
- whitespace/newline;
- quote/apostrophe/backslash/slash/hash;
- `()[]{}`;
- `<`/`>` for `<<< >>>` candidates;
- identifier/number candidate classes.

This follows the useful separation in [simdjson’s two-stage architecture](https://github.com/simdjson/simdjson/blob/master/HACKING.md): identify strings/structural candidates and validate UTF-8 before building the higher representation. For Simple, these bytes are only **candidates** until string/comment/raw masks remove opaque positions.

### 7.4 Malformed UTF handling

- Strict compiler mode: report the canonical invalid span and stop before grammar execution.
- Recovery/tooling mode: create a `RECOVERY | CPU_TODO` task containing the malformed source range and codec state; the CPU recovery policy decides replacement, skipping, and diagnostics.
- GPU code must never silently replace malformed bytes.
- Caches distinguish raw bytes, decoding policy, normalized UTF-8, and recovery policy.

---

## 8. Lexical-state composition and opaque masks

Each chunk computes a total state-transition summary:

```text
F_chunk(entry_state) -> (exit_state, counts, flags)
```

Chunk functions are composed in source order with an associative scan. The approach is supported by the ParPaRaw result: parsing context can be represented as finite-state transformations and composed without an initial whole-input serial context pass. See [ParPaRaw](https://arxiv.org/abs/1905.13415).

### 8.1 GPU-admitted lexical state

Keep the hot lexical state compact and bounded:

```simple
enum LexMode:
    Normal
    DoubleString
    SingleString
    TripleString
    RawString
    LineComment
    BlockComment
    Interpolation
    RawBlockPayload

struct CompactLexState:
    mode: LexMode
    quote_kind: u8
    escape_parity: bool
    interpolation_depth: u16
    raw_delimiter_id: u16
    block_comment_depth: u16
    at_line_start: bool
```

Do not place a dynamic indentation stack in every lexical state. Indentation is computed as a separate line/structure problem after opaque masks and newline discovery.

### 8.2 Known-hard lexical cases

A generated capability manifest gives bounds for:

- maximum raw delimiter variants;
- maximum nested block-comment depth;
- maximum interpolation depth;
- custom lexical hooks;
- maximum finite-state count admitted by each GPU backend.

A region exceeding a bound is tagged `HARD | CPU_TODO` before emission. It is not treated as malformed and is not sent speculatively to a kernel that cannot represent it.

### 8.3 Opaque masks

Only bytes in `Normal` state can contribute ordinary delimiter and token-boundary events. For example, braces in strings, comments, or raw payloads must be removed from the structural candidate masks.

```text
actual_open_brace = candidate_open_brace & ~opaque_mask
actual_close_brace = candidate_close_brace & ~opaque_mask
```

Lexical context resolves cases such as `#`, `//`, and `'`; the UTF classifier itself must not assign their final language meaning.

---

## 9. Structural indexing

### 9.1 Delimiter events and depth

Compact all actual structural events and compute a depth scan over open/close events. For a valid balanced stream:

- an opener is labeled with its depth after opening;
- a closer is labeled with its depth before closing;
- open and close events at the same depth are paired by stable per-depth rank;
- opener and closer kinds are compared to catch cross-kind mismatches such as `([)]`.

Use integer associative scans only. NVIDIA’s [CUB DeviceScan](https://nvidia.github.io/cccl/unstable/cub/api/structcub_1_1DeviceScan.html) and segmented scan contracts are representative primitives; Simple’s runtime should expose backend-neutral scan ports rather than import CUDA types into common contracts.

### 9.2 Delimiter kinds

Initial canonical structural kinds:

```text
Paren        ( ... )
Bracket      [ ... ]
Brace        { ... }
Indent       INDENT ... DEDENT
GpuLaunch    <<< ... >>>
Interpolation
CustomBlock  prefix{ ... }
File         BOF ... EOF
```

Strings and comments are regions and mappings, but they are opaque lexical regions rather than ordinary nested grammar blocks.

### 9.3 Indentation

For each nonblank, non-comment-only line:

1. compute the first code byte and indentation column;
2. validate tab/space policy;
3. find the nearest preceding line with lower indentation;
4. derive the parent line and block end;
5. emit `INDENT`/`DEDENT` events in deterministic line order.

The nearest-smaller-parent computation is GPU-eligible. Inconsistent indentation is a syntax-recovery task; valid indentation must not force the entire file to CPU.

### 9.4 Structural result

The structural index should expose both compact event arrays and optional dense bitmaps. JSON projects such as [Pison](https://github.com/AutomataLab/Pison) demonstrate the utility of leveled structural indexes; [cuJSON](https://github.com/AutomataLab/cuJSON) similarly exposes structural and matching-pair arrays after GPU UTF validation/tokenization/nesting recognition. Simple needs a richer language-specific index, but the representation principle is the same.

---

## 10. Tokenization

### 10.1 Token boundary generation

After opaque masking:

- derive identifier, number, whitespace, operator, punctuation, and delimiter runs;
- resolve multi-byte operators by longest match;
- classify keyword candidates by length/hash/perfect-hash table;
- compact token-start bits with an exclusive scan;
- emit source-backed token spans into exact reserved ranges.

### 10.2 Unicode identifiers

Keep the source UTF-8. ASCII identifiers remain the dominant fast path. Decode a Unicode scalar only at a non-ASCII lead byte, then query generated `XID_Start`/`XID_Continue` tables. Do not convert the whole source to UTF-32.

Identifier normalization is a language-spec decision and must not be introduced as an optimization side effect. Until the Simple specification says otherwise, compare the canonical UTF-8 spelling under the existing identifier rules.

### 10.3 Context-sensitive tokens

The canonical `LexProgram` must own:

- `//` as Simple parallel/composition syntax where applicable;
- line-comment rules;
- `#` comment/attribute/hash decisions;
- apostrophe string versus transpose decisions;
- `<<<`/`>>>` kernel launch tokens;
- raw/triple/interpolated strings;
- array suffixes and custom literal prefixes;
- custom block start/payload/end tokens.

No consumer may reproduce these decisions with ad-hoc `starts_with`, line splitting, or its own token enum after cutover.

---

## 11. Function, statement, and expression mapping

The mapping stage creates a parse skeleton, not an AST.

### 11.1 Inputs

- compact tokens;
- delimiter pairs;
- indentation parents/ends;
- top-level keyword hints;
- lexical entry/exit state hashes;
- embedded/custom block registration.

### 11.2 Outputs

```text
Root/File
  Module or top-level declaration regions
    Type/trait/impl regions
    Function regions
      Parameter-list region
      Body region
        Statement regions
          Expression regions
```

A `kind_hint` is not trusted until the grammar executor accepts it. A region carries a specific grammar entry rule and exact token bounds.

### 11.3 Why this makes direct HIR practical

Once a statement region is bounded, a worker does not need to rediscover the enclosing function, delimiter matching, or statement end. For:

```simple
val x = a + b * c
```

one local parser can count and emit:

```text
VarDecl(x)
  Add
    Ref(a)
    Mul
      Ref(b)
      Ref(c)
```

with unresolved global `NameKey`s. The hard part is not creating HIR records; it is global binding and malformed-input recovery, which remain CPU-owned.

---
## 12. GPU offload plus CPU tagged-table processing

This is the central hybrid-execution contract.

### 12.1 Two tables, two purposes

Use both:

1. **Generated `FrontendCapabilityMap`:** static support status for every lexical state, grammar opcode, action opcode, region kind, and dialect extension. It lets the dispatcher mark known-hard work before executing a GPU kernel.
2. **Runtime `FrontendWorkTable`:** one row per chunk/region/stage work item, with current disposition, reason, handler, input mappings, counts, ranges, provenance, and hash.

The capability map is a development and admission artifact. The work table is an execution artifact.

### 12.2 Generated capability map

```simple
enum BackendSupport:
    Supported
    HardCpu
    Unimplemented
    Experimental
    Forbidden

struct FrontendCapabilityRecord:
    capability_id: u32
    dialect_id: u32
    program_kind: u16       # lex/structure/region/grammar/action
    opcode_or_rule: u32
    scalar: BackendSupport
    simd: BackendSupport
    gpu: BackendSupport
    cpu_handler_id: u16
    reason: WorkReason
    plan_task_id: u32
    evidence_digest: Hash256

struct FrontendCapabilityMap:
    grammar_digest: Hash256
    records: ObjectRef<FrontendCapabilityRecordArena>
```

`plan_task_id` links a runtime limitation to the implementation-plan table. It is not required for execution and can be stripped from a release-minimal manifest if the stable reason/capability IDs are retained.

### 12.3 Runtime work tags

```simple
val WORK_CPU_TODO: u32      = 1u32 << 0
val WORK_HARD: u32          = 1u32 << 1
val WORK_FAIL: u32          = 1u32 << 2
val WORK_RECOVERY: u32      = 1u32 << 3
val WORK_GLOBAL_NAME: u32   = 1u32 << 4
val WORK_RETRYABLE: u32     = 1u32 << 5
val WORK_FATAL: u32         = 1u32 << 6
val WORK_DONE: u32          = 1u32 << 7
val WORK_INVALIDATED: u32   = 1u32 << 8
val WORK_ORACLE_CHECK: u32  = 1u32 << 9
```

The terms have strict meanings:

| Tag | Meaning | Normal action |
|---|---|---|
| `CPU_TODO` | A CPU handler must execute this row. | Compact into the CPU queue. |
| `HARD` | A known capability/admission limit was detected before accelerated emission. | CPU count and emit for this region; not an error. |
| `FAIL` | An attempted executor failed or violated an invariant. | Retry only if explicitly safe; otherwise discard staging output and rerun affected stage on CPU. |
| `RECOVERY` | Source is malformed or incomplete and requires recovery policy. | CPU recovery parser; may emit synthetic nodes/tokens marked recovered. |
| `GLOBAL_NAME` | Cross-scope/module name binding is required. | CPU global binder; expected architecture path. |
| `RETRYABLE` | Failure is transient and the request policy permits retry. | Retry once under bounded policy, then CPU/error. |
| `FATAL` | No trustworthy result can be produced under the selected policy. | Abort request; never publish partial output. |
| `ORACLE_CHECK` | This row is selected for legacy/canonical differential verification. | Execute comparison path and record normalized diff. |

`HARD`, `RECOVERY`, and `GLOBAL_NAME` are not counted as GPU kernel failures. Metrics must keep these categories separate.

### 12.4 Work stages and reasons

```simple
enum FrontendWorkStage:
    Decode
    UtfValidateClassify
    LexState
    Structure
    Tokenize
    RegionMap
    ParseDecl
    ParseStmt
    ParseExpr
    EmitParsedHir
    LocalBind
    TypeConstraint
    GlobalName
    ErrorRecovery
    SemanticResume
    Commit

enum WorkReason:
    None

    # Designed CPU boundaries
    DesignGlobalName
    DesignErrorRecovery

    # Known-hard/admission cases
    UnsupportedEncoding
    LexStateCardinalityExceeded
    DynamicDelimiterUnsupported
    CommentDepthExceeded
    InterpolationDepthExceeded
    NestingDepthExceeded
    IndentPolicyComplex
    RegionStackExceeded
    LongExpressionPolicy
    UnsupportedGrammarOpcode
    UnsupportedActionOpcode
    DialectCpuHookRequired
    BackendIndexWidthExceeded
    CapacityBoundExceeded

    # Source/recovery cases
    MalformedUtf
    UnterminatedString
    UnterminatedComment
    DelimiterMismatch
    InvalidIndentation
    UnexpectedToken
    IncompleteInteractiveInput

    # Executor failures
    DeviceUnavailable
    DeviceLost
    KernelLaunchFailed
    KernelExecutionFailed
    OutputUnderfill
    OutputOverfill
    ReferenceValidationFailed
    DeterminismMismatch
    OracleMismatch

    # Cache/incremental failures
    CacheMiss
    CacheStale
    CacheCorrupt
    GrammarDigestMismatch
    RuntimeAbiMismatch
    PriorSnapshotStale
    StabilizationLimitExceeded

    # Internal fail-closed cases
    InvalidWorkState
    MissingCpuHandler
    InternalInvariant
```

Reason IDs are stable serialized values. Human messages are looked up separately so cache/receipt hashes do not depend on localized text.

### 12.5 Work table schema

```simple
struct FrontendWorkTable:
    # Identity and ordering
    task_id: [u32]
    snapshot_slot: [u32]
    dialect_id: [u32]
    stage: [u16]
    region_id: [u32]
    stable_ordinal: [u32]

    # Input mappings
    byte_start: [u64]
    byte_end: [u64]
    token_start: [u32]
    token_count: [u32]
    parent_task: [u32]
    dependency_start: [u32]
    dependency_count: [u32]

    # Dispatch and state
    tags: [u32]
    reason: [u16]
    requested_backend: [u8]
    executed_backend: [u8]
    cpu_handler_id: [u16]
    attempt_count: [u8]
    priority_class: [u8]

    # Continuation and admission
    entry_state_hash: [Hash128]
    expected_exit_state_hash: [Hash128]
    capability_id: [u32]
    required_stack: [u32]
    required_scratch_bytes: [u64]

    # Count pass
    output_count_slot: [u32]

    # Emit reservation
    output_range_slot: [u32]

    # Validation/provenance
    input_digest: [Hash256]
    output_digest: [Hash256]
    receipt_slot: [u32]
```

The variable dependency lists, counts, ranges, and receipts are flat companion arenas. No row contains nested dynamic arrays.

### 12.6 Output count and range tables

```simple
struct TaskOutputCounts:
    tokens: [u32]
    regions: [u32]
    syntax_nodes: [u32]
    syntax_children: [u32]
    hir_nodes: [u32]
    hir_operands: [u32]
    name_occurrences: [u32]
    constraints: [u32]
    tags: [u32]
    mappings: [u32]
    diagnostics: [u32]

struct TaskOutputRanges:
    # One start/count pair for every column family above.
    token_start: [u64]
    token_count: [u32]
    region_start: [u64]
    region_count: [u32]
    hir_start: [u64]
    hir_count: [u32]
    # ... syntax, children, operands, names, constraints, tags, mappings, diags
```

All arithmetic is checked before truncation to backend index widths. An overflow changes the task disposition; it does not wrap or clip.

### 12.7 CPU TODO compaction

GPU/SIMD admission writes task tags. Then:

```text
predicate[i] = (tags[i] & WORK_CPU_TODO) != 0
exclusive_scan(predicate) -> queue_offset
scatter task_id -> CpuTodoIndex
```

```simple
struct CpuTodoIndex:
    task_ids: [u32]
    design_range: OutputRange
    hard_range: OutputRange
    recovery_range: OutputRange
    failed_range: OutputRange
    global_name_range: OutputRange
    fatal_range: OutputRange
```

Within each class, task IDs remain sorted by:

```text
(priority_class, byte_start, stable_ordinal, task_id)
```

The host reads only the compact count, class offsets, task IDs, and the referenced input slices. In resident mode, it must not read back the entire token/region/HIR arena merely to discover CPU work.

### 12.8 Hybrid count/scan/emit protocol

The safe protocol is:

```text
1. build RegionTable and FrontendWorkTable
2. generated capability admission marks known CPU tasks
3. GPU/SIMD count all admitted accelerated tasks
4. compact CPU_TODO
5. CPU counts hard/recovery tasks using the same grammar/action programs
6. combine every task's counts in stable ordinal order
7. checked exclusive scans reserve all global output ranges
8. GPU emits accelerated tasks into its exact disjoint ranges
9. CPU emits CPU_TODO tasks into their exact disjoint ranges
10. validate fill counts, references, entry/exit states, hashes, and mappings
11. ordered commit publishes one immutable result
```

This solves a common fallback problem: a CPU region does not append an unknown-size patch after GPU output. It participates in the count phase before global reservation.

### 12.9 Late failure policy

Known-hard cases should be discovered no later than count/admission. A failure after output reservation is more serious:

- `OutputUnderfill`, `OutputOverfill`, invalid references, or deterministic-hash mismatch: discard the complete private stage output. Do not fill holes with defaults and do not publish unaffected-looking rows.
- Device loss or kernel execution failure: discard the private stage output. Under `AllowFullCpu`, rerun that stage through canonical scalar/SIMD CPU; under `RequireRequested`, return an error.
- A task-level semantic refusal discovered in GPU count may be retagged `HARD | CPU_TODO` and counted by CPU before reservation.
- A grammar/action refusal discovered only during emit is an executor defect. Record the task as `FAIL | FATAL` for that staging run and fix admission/count parity.

The work table still records the failed task and reason, but partial accelerated artifacts are not trusted.

### 12.10 CPU handler table

```simple
struct CpuHandlerRecord:
    handler_id: u16
    stage: FrontendWorkStage
    dialect_id: u32
    implementation: CpuHandlerKind
    capability_id: u32

enum CpuHandlerKind:
    CanonicalScalarProgram
    CanonicalSimdProgram
    LegacySimpleRegionAdapter
    RecoveryProgram
    GlobalNameBinder
    DialectExtension
```

The GPU stores only `handler_id`; it never stores or calls host function pointers. Missing handlers are fail-closed.

### 12.11 Work mappings

Every task is traceable in both directions:

```text
raw source
  -> normalized UTF-8 span
  -> token span
  -> structural/region ID
  -> work task
  -> syntax/Parsed-HIR output range
  -> global binding/type result
  -> diagnostic or final HIR
```

Add mapping kinds:

```simple
enum FrontendMappingKind:
    RawToNormalized
    NormalizedToToken
    TokenToRegion
    RegionToWork
    WorkToSyntax
    WorkToParsedHir
    ParsedHirToNameOccurrence
    NameOccurrenceToBinding
    ParsedHirToTypedHir
    LegacyAstToParsedHir
    OldRegionToNewRegion
    RecoveryAnchorToSyntheticNode
```

CPU handlers locate exactly the required source/token/region data through these IDs. They must not rescan the whole file merely because one region is hard.

### 12.12 Runtime TODO telemetry

Each compile/parse receipt records:

- total tasks and bytes;
- GPU/SIMD/scalar task counts;
- `HARD`, `FAIL`, `RECOVERY`, and `GLOBAL_NAME` counts separately;
- bytes and HIR nodes processed by CPU fallback;
- reason histogram;
- largest fallback region;
- count, emit, transfer, synchronization, and CPU drain times;
- whether output was legacy-oracle verified;
- deterministic input/output roots.

The CI dashboard should make unexpected hard/fail reasons regressions. A valid canonical corpus may contain `GLOBAL_NAME`; it should contain no `RECOVERY`, no `FAIL`, and—after GPU feature completion—no unexpected `HARD` rows.

---

## 13. Region grammar execution and direct HIR

### 13.1 Real `ParseDialect` v2

```simple
struct ParseDialect:
    identity: ParseDialectIdentity
    encoding_policy: EncodingPolicyRef
    lex_program: LexProgramRef
    structure_program: StructureProgramRef
    region_program: RegionProgramRef
    grammar_program: GrammarProgramRef
    action_program: ActionProgramRef
    recovery_program: RecoveryProgramRef?      # CPU only
    capability_map: FrontendCapabilityMapRef
    tag_schema: TagSchemaRef
    mapping_policy: MappingPolicyRef
    incremental_policy: IncrementalPolicyRef
```

The programs are immutable flat data descriptors. They contain integer IDs/opcodes and constant-table spans, not language-level closures, host pointers, or backend handles.

### 13.2 Grammar execution strategy

The Simple grammar should compile to a deterministic region-local stack machine:

- declaration/statement programs use explicit bounded stacks;
- expression programs use precedence/Pratt-style opcodes and explicit operator/value stacks;
- delimiter and region endpoints are already supplied by the structural map;
- semantic actions are countable and replayable;
- every action has a pure count form and an emit form;
- one warp/subgroup may process a large region; many small regions are packed across lanes/workgroups.

The grammar representation should permit a future parallel operator-precedence path for unusually large expressions or list-like regions. Research on locally parsable and associative operator-precedence parsing shows why bounded context can expose more parallelism, but the initial production path need not make every single expression internally parallel. Parallelism across the many mapped expressions/statements/functions is already substantial.

### 13.3 Action program

Example conceptual opcodes:

```text
BEGIN_NODE kind
END_NODE
EMIT_CHILD child_temp
EMIT_LITERAL token
EMIT_NAME token, occurrence_kind
DECLARE_LOCAL token, declaration_kind
REFERENCE_LOCAL_OR_GLOBAL token
NEW_TYPE_VAR
EMIT_CONSTRAINT relation
EMIT_TAG key, value
EMIT_MAPPING mapping_kind
CALL_DIALECT_BLOCK dialect_id, entry_rule
MARK_CPU_REQUIRED capability_id, handler_id
```

Action programs cannot allocate arbitrary objects. They write only into ranges reserved for their task.

### 13.4 Optional syntax, mandatory Parsed HIR

`ParseOutputMask` determines whether a consumer needs:

- tokens;
- structural regions;
- concrete syntax nodes;
- Parsed HIR;
- tags/mappings/indexes;
- diagnostics.

Compiler and interpreter production paths should request Parsed HIR and omit a full CST/AST unless tooling or diagnostics require it. Tree-sitter requests its own CST. Debug/verification mode may request both syntax and HIR.

### 13.5 Local binding on GPU

For each function/type/local scope:

1. emit declarations and references into `NameOccurrenceTable`;
2. sort or hash by `(scope_id, name_key, source_order)`;
3. detect duplicate locals and shadowing facts;
4. bind references to the nearest valid local declaration;
5. leave imports, module members, external names, global overload sets, and unresolved qualified paths as global-name tasks.

The GPU can emit semantic error facts such as duplicate local declarations. CPU diagnostic arbitration formats and orders user-visible diagnostics; syntax recovery remains separate.

### 13.6 CPU global-name stage

The CPU consumes compact global-name rows, module/import/export/interface hashes, and dependency indexes:

```simple
struct GlobalNameWorkTable:
    occurrence_id: [u32]
    module_id: [u32]
    scope_id: [u32]
    name_key: [u32]
    qualification_start: [u32]
    qualification_count: [u32]
    use_kind: [u16]
    source_hir: [u32]
    stable_ordinal: [u32]

struct GlobalBindingTable:
    occurrence_id: [u32]
    binding_kind: [u16]
    symbol_id: [u64]
    candidate_start: [u32]
    candidate_count: [u32]
    status: [u16]
```

The CPU owns module graph ordering, imports, visibility, cross-file symbol identity, global overload candidate construction, and ambiguous/unresolved global diagnostics. It returns flat binding/candidate tables rather than mutating HIR objects.

### 13.7 GPU semantic resume

After CPU binding:

- apply `GlobalBindingTable` to Parsed HIR;
- generate or resume type constraints dependent on global signatures;
- solve eligible type/trait/overload constraints in deterministic worklists;
- emit `TypedHirArena` and semantic tags;
- place any unsupported solver operation into the ordinary hard-task table until it gains GPU support.

The architectural exceptions remain global-name binding and syntax recovery. Transitional unsupported semantic operations may use CPU tasks, but their capability records must be marked `Unimplemented`/`HardCpu` and driven toward zero on the full valid-source corpus.

### 13.8 Three useful HIR states

```text
Parsed HIR
    syntax fixed, source mapped, locals bound, globals represented as NameKey

Bound HIR
    CPU GlobalBindingTable applied, global symbol/candidate IDs known

Typed HIR
    type/trait/overload constraints resolved, ready for existing HIR/MIR pipeline
```

This split removes the false assumption that HIR cannot be emitted until every global name is known.

---

## 14. SIMD optimization plan

SIMD is not a lesser unrelated implementation. It is the CPU-vector executor for the same masks, summaries, tables, grammar programs, work rows, and output ranges.

### 14.1 Representation reuse

Scalar, SIMD, and GPU share:

- `SourceSnapshot` and byte offsets;
- `UtfClassBlock` masks;
- chunk transition summaries;
- opaque masks;
- delimiter/indent indexes;
- `TokenArena`;
- `RegionTable`;
- `FrontendWorkTable`;
- `TaskOutputCounts/Ranges`;
- grammar/action bytecode;
- Parsed HIR and sidecars;
- semantic hashes and receipts.

This prevents a “fast lexer” from becoming another grammar implementation.

### 14.2 SIMD stages

| Stage | SIMD strategy |
|---|---|
| Decode/transcode | Reuse and centralize existing UTF-8/16/32 SIMD codecs; exact scalar fallback and error offset. |
| UTF validate/classify | Produce validity and lexical candidate masks in 16/32/64-byte blocks. |
| Quote/escape/comment masks | Bitwise escaped-quote and state propagation; carry compact state across blocks. |
| Structure | Mask opaque bytes; compact events; vector count and prefix helpers. |
| Newline/indent | Vector newline discovery and leading whitespace classification; parallel line-parent computation. |
| Token boundaries | Vector class transitions, multi-character operator candidates, ASCII identifiers/numbers. |
| Unicode identifiers | Sparse scalar/vector-table path only for non-ASCII lead bytes. |
| Region map | Parallel over top-level and statement delimiter events; vector keyword/hash probes. |
| Grammar | Task-parallel across regions; subgroup/vector operations inside large expression/list regions where profitable. |
| HIR emission | Exact disjoint ranges; contiguous SoA writes and batched interning. |

### 14.3 CPU ISA dispatch

Use one central runtime dispatch layer. Initial guaranteed paths should match available tested infrastructure, typically scalar plus x86 SSE2/AVX2 and ARM NEON. Add AVX-512, SVE/SVE2, and RISC-V Vector only when the same forced-backend corpus and malformed-input tests pass.

Do not encode CPU ISA names into semantic cache keys. Record implementation and ISA in the receipt/evidence row.

### 14.4 Scalar tails and boundary state

Every SIMD block algorithm must define:

- unaligned prefix/tail handling;
- page/end-of-buffer safety;
- UTF sequence split across blocks;
- quote/backslash runs split across blocks;
- CR/LF split across blocks;
- token split across blocks;
- exact continuation state used for incremental stabilization.

Forced block-size tests should run every possible boundary placement for representative tokens, strings, comments, Unicode scalars, and delimiters.

### 14.5 Fused and unfused kernels

Provide both:

- referenceable logical kernels: UTF validate, classify, opaque mask, structure, tokenize;
- fused fast paths that combine reads when profitable.

Parity tests compare the fused path to the composition of logical kernels. This keeps optimization from hiding semantic coupling.

### 14.6 Auto thresholds

No fixed source-size threshold should be embedded without retained evidence. Selection features include:

- normalized byte count;
- file count/batch count;
- expected token and region density;
- current source/token/HIR residency;
- requested output mask;
- cache hit level;
- GPU queue occupancy;
- transfer/synchronization estimate;
- CPU ISA and core availability;
- observed hard/recovery ratio for the dialect/profile.

A backend is promoted only when parity is established and retained benchmark evidence shows the required speedup. The existing parser/offload design’s `>= 1.5x` median speedup gate is a reasonable default promotion rule, measured end to end for the selected stage rather than kernel time alone.

---

## 15. Unified parser platform

### 15.1 Shared runtime, distinct dialects

```text
ParserSession
  ├─ Source/normalization service
  ├─ ParseRuntime
  │    ├─ scalar executor
  │    ├─ SIMD executor
  │    ├─ GPU executor
  │    ├─ CPU task drain
  │    ├─ ordered commit
  │    └─ incremental planner
  ├─ Cache service
  ├─ Mapping/tag/index service
  └─ Dialect bundle
       ├─ SimpleDialect
       ├─ SdnDialect
       ├─ SoshDialect
       └─ registered embedded dialects
```

### 15.2 Parser session

```simple
struct ParserSessionIdentity:
    provider: ParserProvider
    dialect_id: u32
    dialect_schema: u32
    lex_digest: Hash256
    structure_digest: Hash256
    region_digest: Hash256
    grammar_digest: Hash256
    action_digest: Hash256
    recovery_digest: Hash256
    runtime_abi: u32
    layout_version: u32

struct ParserSession:
    identity: ParserSessionIdentity
    source: SourceSnapshotRef
    prior_source: SourceSnapshotRef?
    prior_result: ParseArtifactSetRef?
    edits: TextEditArenaRef?
    output_profile: ParseOutputProfile
    execution_profile: ExecutionProfile
    cache: ParserCachePortRef
```

The session replaces module-global parser state on the canonical path and provides a migration target for current append/isolated/reset behavior.

### 15.3 Consumer matrix

| Consumer | Dialect/entry rule | Primary output | Recovery contract | Default execution | Migration decision |
|---|---|---|---|---|---|
| Simple compiler | `SimpleDialect.source_file` / module | Parsed/Bound/Typed HIR; optional syntax | Strict valid build; CPU recovery for diagnostic builds | Auto: scalar/SIMD small, GPU batch/resident | Integrate through compiler frontend adapter; retain legacy full CPU path. |
| Simple interpreter | `SimpleDialect.repl_item`, expression, statement, module | Same Typed HIR or interpreter-ready projection | CPU incomplete-input recovery; distinguish “need more input” | Scalar/SIMD for one REPL item; GPU for batch/resident scripts | Remove separate simplified grammars; share Simple grammar and HIR. |
| Native/Wasm Tree-sitter | Generated Simple Tree-sitter grammar | CST/tree and changed ranges | Tree-sitter’s error-tolerant incremental contract | Native or Wasm Tree-sitter runtime | Generated from canonical grammar plus explicit recovery/conflict overlay; never compiler authority. |
| sosh interactive command | `SoshDialect.command` | `ShellHir`/command plan | CPU shell recovery/incomplete quote reporting | Scalar/SIMD | Replace hand scanners while keeping expansion/execution separate. |
| sosh script | `SoshDialect.script` | block/pipeline/redirect/function `ShellHir` | CPU recovery | Auto; GPU useful for batches/large scripts | Replace line-depth parser with shared region/grammar runtime. |
| SDN | `SdnDialect.document` / value | `SdnValueArena` + spans/issues | Strict or CPU recovery by caller | Scalar/SIMD default; GPU for batch/large docs | Current lexer/parser remain oracle until parity; then public API routes through dialect. |
| Embedded block | Registered dialect and entry rule | Dialect-specific IR/raw payload | Dialect policy | Per-block auto | `sh{}` can invoke SoshDialect; other blocks register without changing Simple core parser. |

### 15.4 The Tree-sitter boundary

Tree-sitter is a parser generator and incremental parsing runtime designed to produce useful trees under edits and syntax errors. Its official incremental workflow edits the old tree and passes it into the next parse so unchanged structure can be shared. See [Tree-sitter incremental editing](https://tree-sitter.github.io/tree-sitter/using-parsers/3-advanced-parsing.html).

Therefore:

- native/Wasm Tree-sitter should remain a separate execution provider;
- its Simple grammar must be generated from the canonical grammar source;
- its parser/runtime ABI and query digests belong in Tree-sitter cache identity;
- valid-source acceptance and normalized stable-node mappings must match the canonical Simple grammar;
- invalid/incomplete-source tree shapes are governed by a separate Tree-sitter recovery contract and are not required to equal the compiler’s CPU-recovery tree;
- the current Simple-coded reduced parser must be renamed during migration and must not report `native-tree-sitter` provenance.

### 15.5 Compiler and interpreter unification

The compiler and interpreter should consume the same `SimpleDialect` and the same Parsed HIR schema. Differences belong in:

- entry rule (`source_file`, `repl_item`, expression, statement);
- feature/config profile;
- recovery policy;
- requested output profile;
- downstream execution/code-generation path.

They must not maintain separate token enums, precedence, statement parsing, or declaration grammar.

### 15.6 SDN reuse

`SdnDialect` should use the common runtime for:

- UTF-8 and source spans;
- strings/escapes/comments;
- `{}`, `[]`, indentation/newline regions;
- colon/comma/top-level separator structure;
- token and region arenas;
- count/scan/emit;
- diagnostics, tags, mappings, incremental edits, and caches.

Its `ActionProgram` emits an `SdnValueArena`, not Simple HIR. The existing public `parse_sdn` result can be maintained by an adapter while callers migrate.

### 15.7 sosh reuse

`SoshDialect` must parse before expansion. Its grammar/action program should emit:

- command/word segments preserving quote mode;
- pipelines and boolean/parallel composition;
- redirections and file-descriptor targets;
- background execution;
- variable/command substitutions as structured nodes;
- functions, `if`, loops, and `case` blocks;
- source spans and expansion flags.

Variable expansion, globbing, command lookup, file opening, and process launch remain execution stages. This eliminates repeated quote/backslash scans in command, pipe, redirect, and script modules.

---
## 16. Canonical grammar and divergence control

### 16.1 One authoritative grammar source

Recommended source layout:

```text
grammar/
  schema/
    parser_grammar_schema.sdn
  simple/
    simple_grammar.sdn
    simple_lexical_modes.sdn
    simple_actions.sdn
    simple_tree_sitter_overlay.sdn
    simple_legacy_handler_map.sdn
  sdn/
    sdn_grammar.sdn
    sdn_actions.sdn
  sosh/
    sosh_grammar.sdn
    sosh_actions.sdn
```

SDN is suitable as the declarative format because it is textual, source-mappable, and already part of the project. To avoid a bootstrap cycle, generated parser tables are checked in and are the build inputs. Grammar regeneration is a development/full-bootstrap action performed by an already working tool; the seed/bootstrap compiler never needs to parse the grammar specification to compile itself.

### 16.2 Grammar schema

Each feature/rule should declare at least:

```simple
struct GrammarFeature:
    feature_id: u32
    stable_name: text
    lexical_modes: [LexModeId]
    token_ids: [TokenKindId]
    productions: [ProductionId]
    precedence: PrecedenceSpec?
    associativity: Associativity?
    entry_rules: [GrammarRuleId]
    semantic_actions: [ActionId]
    region_hints: [RegionHint]
    scalar_support: BackendSupport
    simd_support: BackendSupport
    gpu_support: BackendSupport
    legacy_handler: u16
    tree_sitter_projection: TreeSitterProjection?
    conformance_cases: [CorpusCaseId]
```

Stable numeric IDs are generated from a registry, never source-order ordinals that shift when a rule is inserted.

### 16.3 Generated artifacts

One generator emits:

```text
src/lib/common/structural/parse/generated/simple/
  token_ids.spl
  lex_program.spl
  structure_program.spl
  region_program.spl
  grammar_program.spl
  action_program.spl
  capability_map.spl
  feature_manifest.spl

src/compiler/10.frontend/generated/
  legacy_token_adapter.spl
  legacy_rule_coverage.spl
  parsed_hir_action_bindings.spl

tree-sitter-simple/
  grammar.js or grammar.json
  src/parser.c
  src/node-types.json
  src/scanner.c                 # only when required
  queries/highlights.scm
  queries/locals.scm
  test/corpus/*.txt

test/generated/parser/
  simple_valid_manifest.sdn
  simple_invalid_manifest.sdn
  token_id_golden.sdn
  precedence_golden.sdn
  grammar_feature_matrix.sdn
```

Every generated artifact embeds the same:

```text
grammar_digest
schema_version
generator_version
token_registry_digest
action_registry_digest
```

CI regenerates into a temporary directory and rejects any diff.

### 16.4 Tree-sitter projection and overlay

Tree-sitter grammars are conventionally generated from `grammar.js`/structured grammar and produce C parser tables; the official CLI also supports `grammar.json`. See [Tree-sitter parser generation](https://tree-sitter.github.io/tree-sitter/cli/generate.html).

A direct projection from the canonical grammar covers valid syntax. A narrowly scoped overlay may declare:

- Tree-sitter `extras`;
- conflict resolutions;
- aliases and hidden/visible CST nodes;
- external scanner states for indentation/raw delimiters where generation cannot express the lexical rule directly;
- editor-specific recovery precedence;
- supertypes and field names;
- query-visible node groupings.

The overlay may change recovery shape and CST presentation. It must not silently accept a different valid language. Any unavoidable valid-source difference is listed in a versioned `grammar_divergence.sdn` with a feature ID, reason, owner, expiration plan, and test.

### 16.5 Current divergence findings to resolve

| Finding | Consequence | Required correction |
|---|---|---|
| Full compiler grammar, simplified common parser, and reduced “TreeSitterParser” are independent rule bodies. | Valid programs can parse differently by consumer. | Extract one canonical grammar; adapt or generate all consumers. |
| The current reduced “TreeSitterParser” has its own token set and lexer but is not a generated native Tree-sitter parser. | Misleading provider identity and incomplete syntax coverage. | Rename immediately; replace with generated native/Wasm provider. |
| Interpreter exposes both Tree-sitter-wrapper and pure-parser-wrapper paths. | REPL/module behavior can diverge from the compiler. | Route both entrypoints to `SimpleDialect` and preserve only API adapters. |
| SDN parser repeats source scanning rather than consuming only its lexer output. | String/delimiter/indent rules can drift internally. | Generate `SdnDialect`; make one token/structure source of truth. |
| sosh repeats quote/escape logic in several modules. | Different behavior among direct command, pipeline, redirect, and script paths. | Generate `SoshDialect` entry rules and one Shell HIR action sink. |
| Execution modes exist as both enums and text strings. | Cache and dispatch identity can disagree. | One typed enum, one serializer. |
| Current v1 parity hash ignores lexeme bytes and has an empty input hash. | Different source text can look parity-equal if kinds/spans match. | Hash source identity plus all demanded semantic columns and mappings. |
| Frontend preprocessing rewrites/extracts source before parsing. | Source offsets and parser/tooling views can diverge. | Represent preprocessing as active masks/regions with explicit source mappings. |

### 16.6 Grammar conformance matrix

For every grammar feature, generate a row:

```text
FeatureId | CanonicalScalar | CanonicalSIMD | GPU | LegacyCPU |
Interpreter | NativeTS | WasmTS | CorpusValid | CorpusInvalid | Status
```

Statuses:

```text
PASS
EXPECTED_RECOVERY_DIFFERENCE
HARD_CPU_TRANSITIONAL
MISSING
BLOCKED
REMOVAL_PENDING
```

A new Simple syntax feature cannot merge unless:

- canonical grammar and action entries exist;
- legacy full CPU coverage exists or the release policy explicitly permits a temporary gated gap;
- valid corpus cases exist;
- Tree-sitter valid-source projection exists;
- backend capability statuses and CPU handlers are declared;
- cache grammar digest changes;
- generated files are clean.

### 16.7 Valid versus invalid-source parity

Do not compare all parsers under one incorrect rule.

**Valid source:**

- same acceptance;
- same normalized token kinds and byte spans;
- same stable structural/semantic node mapping where that provider emits them;
- same Parsed HIR for compiler/interpreter/canonical backends;
- Tree-sitter CST maps to the same canonical feature IDs and source ranges.

**Invalid or incomplete source:**

- canonical GPU path emits recovery work but does not repair;
- CPU compiler recovery and Tree-sitter recovery may produce different trees;
- each provider must satisfy its declared recovery contract;
- shared invariants still include bounded progress, valid source ranges, deterministic output, no crashes, and truthful provider labels.

Tree-sitter recommends a corpus case for each visible grammar rule; the generated conformance corpus should feed both Tree-sitter’s `test/corpus` format and Simple’s own parser specs. See [Tree-sitter corpus testing](https://tree-sitter.github.io/tree-sitter/creating-parsers/5-writing-tests.html).

### 16.8 Legacy CPU grammar preservation without drift

Preserving the original full CPU frontend does not mean it remains an ungoverned second language definition.

During migration:

1. Generate token IDs/constants from the canonical registry and adapt the legacy lexer/parser to them.
2. Generate `simple_legacy_handler_map.sdn`, mapping each canonical feature/rule to the current parser function(s).
3. Instrument legacy parser output with stable feature IDs and normalized source/HIR mappings.
4. Require the full valid corpus to pass both legacy and canonical scalar paths.
5. Keep the independent handwritten control flow and AST/lowering path so it remains a useful diverse oracle.
6. For every future grammar change, update canonical grammar first; CI identifies missing legacy coverage before merge.

The legacy path can remain permanently while ceasing to be the grammar authority.

---

## 17. Homogenized parser cache system

### 17.1 Cache principle

One cache service owns parser artifacts. Different consumers and backends may request different projections, but they do not invent unrelated key formats or stale-data rules.

The cache separates source identity, normalized text policy, grammar/provider identity, parse products, semantic products, recovery products, and execution evidence.

### 17.2 Cache identity

```simple
struct ParserCacheKey:
    # Source
    raw_source_digest: Hash256
    encoding_policy_digest: Hash256
    normalized_utf8_digest: Hash256
    preprocess_config_digest: Hash256

    # Parser identity
    provider: ParserProvider
    dialect_id: u32
    dialect_schema: u32
    lex_digest: Hash256
    structure_digest: Hash256
    region_digest: Hash256
    grammar_digest: Hash256
    action_digest: Hash256
    recovery_digest: Hash256
    runtime_abi: u32
    storage_layout_version: u32

    # Request semantics
    entry_rule: u32
    feature_config_digest: Hash256
    output_profile_digest: Hash256
    tag_demand: u32
    recovery_policy_digest: Hash256
    consumer_projection: u32
```

After backend parity is certified, `ScalarCpu`, `SimdCpu`, and `Gpu` are not semantic key fields. The artifact receipt records which backend created and verified the payload. During pre-promotion experimentation, an isolated verification namespace may include backend identity to prevent uncertified cross-use.

### 17.3 Artifact layers

| Layer | Artifact | Reusable by |
|---|---|---|
| L0 | Raw immutable `FileBuffer`/source blob | All providers/consumers |
| L1 | Normalized UTF-8 + offset checkpoints | Canonical runtime, Tree-sitter input, tools |
| L2 | UTF class and newline blocks | Scalar/SIMD/GPU canonical dialects |
| L3 | Lex-state summaries and opaque masks | Canonical dialect backends |
| L4 | Structural index/pairs/indent table | Canonical dialect backends and tooling |
| L5 | Token arena | Compiler, interpreter, SDN/sosh adapters where dialect matches |
| L6 | Region/work map | Canonical runtime and incremental planner |
| L7 | Syntax/Parsed-HIR segments | Compiler/interpreter/tooling by output profile |
| L8 | Global binding table | Compiler/interpreter sharing the same dependency/interface state |
| L9 | Typed HIR/consumer projection | Matching compile/runtime profiles |
| LR | Recovery/diagnostic artifact | Matching recovery and diagnostic policy only |
| LT | Native/Wasm Tree-sitter old tree/session state | Same document, language ABI, runtime/provider, and edit lineage |
| LE | Backend performance/evidence rows | Auto dispatcher; never semantic output |

### 17.4 Explicit artifact IDs

Keep distinct identities instead of one overloaded “parse cache key”:

```text
raw_id
text_policy_id
normalized_source_id
utf_class_id
lex_state_id
structure_id
token_id
region_map_id
work_map_id
syntax_id
parsed_hir_id
global_binding_id
typed_hir_id
diagnostic_id
tree_sitter_tree_id
semantic_policy_id
```

This permits a grammar change to invalidate parsing without redoing UTF normalization, and a global dependency change to invalidate binding/typing without retokenizing unchanged source.

### 17.5 Region-level cache key

```simple
struct ParseSegmentCacheKey:
    parser_identity_digest: Hash256
    region_content_digest: Hash256
    entry_rule: u32
    entry_state_hash: Hash128
    expected_exit_state_hash: Hash128
    parent_context_digest: Hash256
    feature_config_digest: Hash256
    output_profile_digest: Hash256
```

A region is reusable only when lexical/grammar context stabilizes at its boundary. Matching source bytes alone are insufficient for a token sequence whose interpretation depends on an earlier unclosed string/comment/interpolation.

### 17.6 Storage hierarchy

```text
L1: device/Object-VM resident CAS
    masks, indexes, tokens, regions, work rows, Parsed/Typed HIR

L2: host memory CAS
    active session artifacts, CPU work inputs/results, native tree handles

L3: disk/SMF content-addressed cache
    normalized source, stable tables, segments, HIR, mappings, receipts

L4: optional SSD/direct-storage placement
    large immutable batches and resident compiler snapshots
```

All layers use the same logical artifact key and schema. Placement is metadata; it is not semantic identity.

### 17.7 Incremental invalidation

Given edits:

1. update the immutable source snapshot;
2. expand to UTF sequence and lexical checkpoint boundaries;
3. recompute affected class/lex blocks;
4. continue until entry/exit lexical state and structural summaries stabilize;
5. rebuild affected delimiter/indent/token ranges;
6. map edits to changed regions;
7. reuse unchanged region artifacts by reference;
8. update old-to-new region/node mappings;
9. invalidate global binding only when exported/imported interface hashes or affected name sets change;
10. invalidate diagnostics/recovery under their separate policy keys.

The current `incremental.spl` stub becomes the planner for these immutable segments. A “full reparse then deduplicate” implementation does not satisfy this contract.

### 17.8 Tree-sitter session cache

Native Tree-sitter tree handles are process/runtime objects, not portable disk payloads. Store them in the parser session and follow Tree-sitter’s required workflow:

1. edit the old tree with the exact byte/point edit;
2. parse with that old tree;
3. obtain changed ranges;
4. map changed ranges into the shared invalidation graph;
5. cache stable canonical projections separately if persistence is needed.

A native tree from another grammar digest, language ABI, runtime ABI, or document lineage is stale and cannot be reused.

### 17.9 Existing compiler parse-cache migration

The current flat-pool frontend cache should migrate in three steps:

1. Wrap existing blobs as `LegacyAstCacheArtifact` with explicit parser/provider/grammar/source/codec/layout identity.
2. Publish them through the common cache port and preserve current fail-closed corruption behavior.
3. Add canonical token/region/Parsed-HIR artifacts; prefer the deepest valid common layer.
4. Stop writing new legacy blobs only after compiler bootstrap and rollback gates pass; retain reading support for a bounded cache-version window if useful.

### 17.10 Cache validation

Every payload validates:

- schema and layout version;
- complete key/digest match;
- array column lengths;
- index/reference bounds;
- source span bounds;
- output deterministic hash;
- dependency/interface digest set;
- provider truthfulness;
- optional CPU-oracle verification stamp.

A mismatch is a miss or a hard cache error according to policy, never a best-effort partial restore.

---

## 18. Required Simple compiler-layer refactoring

The GPU design cannot be bolted onto the current module-global parser and object-oriented action path. The Simple layer must expose GPU-compatible, CPU-friendly contracts.

### 18.1 Make parser state explicit and reentrant

Replace module-global current token, scope, AST pool, resource/effect/aspect registries, and reset flags on the canonical path with:

```simple
struct SimpleParserSessionState:
    token_cursor: u32
    module_id: u32
    scope_stack: ObjectRef<U32Arena>
    feature_config: FeatureConfigRef
    resource_registry: ResourceRegistryRef
    effect_registry: EffectRegistryRef
    aspect_registry: AspectRegistryRef
    output_sink: ParseActionSinkRef
```

The legacy parser may initially populate this structure through adapters while preserving its behavior. Canonical scalar/SIMD/GPU execution must not depend on module globals.

### 18.2 Refactor preprocessing into mapped structure

Current line-based conditional preprocessing/domain-block extraction should become:

```simple
struct PreprocessResult:
    active_byte_mask: ObjectRef<BitBlockArena>
    inactive_regions: ObjectRef<SourceRegionArena>
    custom_block_regions: ObjectRef<CustomBlockRegionArena>
    source_mappings: MappingShardRef
    config_digest: Hash256
```

Do not rewrite text and lose original source positions. Simple conditionals that are table-evaluable can run on GPU/SIMD. Dynamic/plugin preprocessing that is not yet representable is tagged as a CPU task with exact mappings.

### 18.3 Make HIR flat and parse-emittable

The downstream HIR interface must accept stable arena IDs, child/operand spans, unresolved/bound name IDs, type variables, and sidecar refs. It must not require a pointer-linked AST walk as the only construction mechanism.

During migration provide both adapters:

```text
Legacy AST pools -> normalized Parsed HIR
Canonical Parsed HIR -> temporary legacy AST pools/bridge, where required
```

The second adapter allows downstream compiler layers to remain unchanged while the new parser matures. It is removed only when every necessary consumer accepts Parsed/Typed HIR directly.

### 18.4 Countable semantic actions

Every Simple grammar action must define:

- output counts;
- output emission into reserved ranges;
- required token/region inputs;
- produced tags/mappings/indexes;
- local/global name facts;
- possible diagnostics;
- backend capability and CPU handler;
- deterministic ordering.

Actions that call arbitrary host code or allocate dynamic object graphs are CPU hooks and appear in the capability/work tables until refactored.

### 18.5 Custom block registry

```simple
struct EmbeddedDialectRegistration:
    prefix_token: u16
    dialect_id: u32
    entry_rule: u32
    payload_mode: u16
    result_projection: u16
    capability_id: u32
```

`m{}`, `loss{}`, `sh{}`, `sql{}`, and future blocks become nested dialect requests over an already paired source region. This removes custom-block special cases from the Simple core grammar while retaining typed integration actions.

### 18.6 Correct semantic fingerprinting

The v2 deterministic root must include, according to requested outputs:

- normalized source digest;
- dialect/grammar/action/schema identity;
- token kinds and source-backed lexeme identity;
- structural pairs/region records;
- syntax/Parsed-HIR columns and edges;
- name occurrences/bindings;
- type constraints/results;
- demanded tags, mappings, indexes, and diagnostics;
- recovery/synthetic flags;
- feature/preprocess configuration.

`StageReceipt.input_hash` must never be empty for a published v2 artifact.

### 18.7 Unify execution-mode contracts

Move to one common typed set and convert only at boundaries:

```simple
enum ParseExecutionMode:
    CpuReference
    HybridVectorGpu
    ResidentGpu
    Auto
```

Backend selection within hybrid mode uses `ParseBackend`. Remove independent string comparisons from runtime hot paths after compatibility migration.

---

## 19. Proposed source layout and ownership

Use the existing structural-compute ownership instead of creating a separate parser subsystem.

```text
src/lib/common/structural/parse/
  contracts_v1.spl                 # frozen compatibility
  contracts_v2.spl
  source_snapshot.spl
  dialect.spl
  grammar_schema.spl
  token_arena.spl
  structural_tables.spl
  region_table.spl
  work_table.spl
  output_plan.spl
  parsed_hir.spl
  mappings.spl
  cache_identity.spl
  receipts.spl
  generated/
    simple/
    sdn/
    sosh/

src/lib/nogc_async_mut/structural/parse/
  runtime.spl
  scalar/
    decode.spl
    lex_structure.spl
    grammar_vm.spl
    action_emit.spl
  simd/
    dispatch.spl
    utf_classify.spl
    opaque_mask.spl
    structure.spl
    tokenize.spl
    region_map.spl
    grammar_vm.spl
  gpu/
    admission.spl
    decode_utf.spl
    utf_classify.spl
    lexical_state.spl
    structure.spl
    indentation.spl
    tokenize.spl
    region_map.spl
    grammar_count.spl
    grammar_emit.spl
    local_bind.spl
    semantic_resume.spl
  cpu_task/
    compact.spl
    count.spl
    emit.spl
    recovery.spl
    global_name.spl
    ordered_commit.spl
  incremental/
    planner.spl
    stabilization.spl
    mapping.spl
  cache/
    port.spl
    memory.spl
    resident_gpu.spl
    disk_cas.spl
  auto_profile.spl

src/compiler/10.frontend/
  provider.spl
  structural_adapter/
    parse_request.spl
    legacy_oracle.spl
    legacy_ast_adapter.spl
    parsed_hir_adapter.spl
    preprocess_adapter.spl
  generated/

src/app/interpreter/
  parser_adapter.spl
  repl_parse_session.spl

src/os/apps/shell/parser/
  dialect_adapter.spl
  shell_hir.spl
  execution_adapter.spl

src/lib/common/sdn/
  dialect_adapter.spl
  value_sink.spl
  legacy_parser_adapter.spl

tree-sitter-simple/
  grammar.js
  src/parser.c
  src/scanner.c
  src/node-types.json
  queries/
  test/corpus/
```

Mutation/ownership variants should import or mechanically regenerate the same common dialect tables. They must not contain copied grammar definitions.

---

## 20. Implementation plan

### Status vocabulary

| Status | Meaning |
|---|---|
| `PRESERVE` | Existing implementation remains as an oracle or compatibility path. |
| `ADAPT` | Existing code remains but is placed behind a new contract. |
| `IMPLEMENT` | Missing functionality. |
| `REPLACE_AFTER_GATE` | New implementation becomes default only after explicit parity/performance gates. |
| `DELETE_AFTER_GATE` | Duplicate rule bodies/ad-hoc scans are deleted only after all dependents migrate. |
| `BLOCKER` | Backend work must not proceed past the named gate. |

### Phase 0 — Freeze baseline and create full inventories

| ID | Status | Task | Exit evidence |
|---|---|---|---|
| GFPU-000 | `PRESERVE` | Pin the current full compiler frontend and bootstrap corpus as `SimpleLegacyCpu`. | Reproducible baseline hashes and compile/test commands. |
| GFPU-001 | `IMPLEMENT` | Inventory every Simple token, lexical mode, precedence, declaration, statement, expression, action, custom block, and recovery rule across compiler/common/interpreter/current tree parser. | Generated `grammar_inventory.sdn`; zero unowned entries. |
| GFPU-002 | `IMPLEMENT` | Inventory sosh scanners/rules and SDN lexer/direct scans. | `sosh_inventory.sdn`, `sdn_inventory.sdn`. |
| GFPU-003 | `IMPLEMENT` | Build valid, invalid, incomplete, Unicode, custom-block, and bootstrap corpus manifests. | Stable corpus IDs and expected providers. |
| GFPU-004 | `IMPLEMENT` | Measure current CPU parse/token/HIR/cache performance and memory by file size and batch. | Retained evidence dataset keyed by commit/toolchain/hardware. |
| GFPU-005 | `BLOCKER` | No GPU grammar executor implementation before v2 contracts, IDs, and oracle normalization are frozen. | Architecture review approval. |

### Phase 1 — Parser contract v2 and compatibility

| ID | Status | Task | Exit evidence |
|---|---|---|---|
| GFPU-100 | `IMPLEMENT` | Create v2 source, token, structure, region, work, output, Parsed-HIR, mapping, and receipt schemas. | Golden binary/SDN vectors and column validators. |
| GFPU-101 | `ADAPT` | Freeze v1 lexical contracts and expose explicit v1-to-v2 adapter. | Existing v1 unit/system specs unchanged. |
| GFPU-102 | `IMPLEMENT` | Unify mode enum/string serialization and provider/backend identity. | One canonical mode definition; compatibility parser for old config text. |
| GFPU-103 | `IMPLEMENT` | Implement semantic input/output roots; populate nonempty input hashes. | Mutation tests prove lexeme/source differences change the proper root. |
| GFPU-104 | `IMPLEMENT` | Replace mandatory copied source construction with borrowed/owned immutable byte views. | Allocation/copy counters and lifetime tests. |
| GFPU-105 | `IMPLEMENT` | Implement exact reserved action sink and count/range validators. | Deliberate underfill/overfill tests fail closed. |
| GFPU-106 | `IMPLEMENT` | Implement capability map and work/cause/tag registries. | Generated registry golden file; stable IDs. |

### Phase 2 — Canonical grammar source and generator

| ID | Status | Task | Exit evidence |
|---|---|---|---|
| GFPU-200 | `IMPLEMENT` | Define grammar SDN schema, stable token/rule/action/feature registries. | Schema validator and round-trip tests. |
| GFPU-201 | `IMPLEMENT` | Mechanically extract the current full Simple valid grammar into canonical specification. | Legacy corpus coverage report; no undocumented production. |
| GFPU-202 | `IMPLEMENT` | Generate lexical/structure/region/grammar/action programs and capability map. | Generated-table deterministic hashes. |
| GFPU-203 | `ADAPT` | Generate compiler legacy token constants and feature-to-handler coverage map. | Legacy parser builds with generated IDs. |
| GFPU-204 | `IMPLEMENT` | Generate Tree-sitter grammar, scanner inputs, node mapping, and corpus. | `tree-sitter generate` and `tree-sitter test` clean. |
| GFPU-205 | `IMPLEMENT` | Generate grammar feature/conformance/divergence matrix. | CI blocks missing valid-source coverage. |
| GFPU-206 | `BLOCKER` | No duplicate hand-written Simple grammar may become a new dependency after this phase. | Dependency/lint rule. |

### Phase 3 — Normalize and retain the original full CPU frontend

| ID | Status | Task | Exit evidence |
|---|---|---|---|
| GFPU-300 | `PRESERVE` | Keep the current compiler parser/AST/desugar/lowering path under `SimpleLegacyCpu`. | CPU-only build and full bootstrap pass. |
| GFPU-301 | `ADAPT` | Add `ParserSession` facade and normalized source/token/feature mappings around legacy global state. | Reentrant sequential sessions; no cross-session leakage. |
| GFPU-302 | `IMPLEMENT` | Normalize legacy AST/HIR output to canonical feature IDs and semantic roots. | Differential comparator produces actionable first-difference paths. |
| GFPU-303 | `ADAPT` | Put current flat AST cache behind common cache identity as `LegacyAstCacheArtifact`. | Old behavior retained, stale/corrupt cache remains fail-closed. |
| GFPU-304 | `IMPLEMENT` | Add explicit `--frontend=legacy-cpu` and API provider selection. | No GPU/runtime initialization in legacy mode. |

### Phase 4 — Canonical scalar full parser

| ID | Status | Task | Exit evidence |
|---|---|---|---|
| GFPU-400 | `IMPLEMENT` | Implement scalar UTF validation/classification over v2 source snapshots. | Full Unicode/malformed corpus parity. |
| GFPU-401 | `IMPLEMENT` | Implement scalar lexical-state summaries and opaque masks. | Every chunk split matches whole-source oracle. |
| GFPU-402 | `IMPLEMENT` | Implement scalar delimiter pairing and indentation structure. | Balanced/mismatched/deep/blank/comment tests. |
| GFPU-403 | `IMPLEMENT` | Implement scalar token and region map. | Token/region golden tables for full Simple corpus. |
| GFPU-404 | `IMPLEMENT` | Implement scalar grammar/action VM and direct Parsed HIR. | Valid corpus semantic parity with legacy CPU. |
| GFPU-405 | `IMPLEMENT` | Implement scalar local binding and type-constraint generation. | Local scope/shadow/duplicate tests. |
| GFPU-406 | `IMPLEMENT` | Implement CPU global-name table stage and semantic resume interface. | Cross-module/bootstrap name parity. |
| GFPU-407 | `IMPLEMENT` | Implement CPU recovery program separately from valid grammar. | Invalid/incomplete corpus deterministic and bounded. |

### Phase 5 — SIMD parser integration

| ID | Status | Task | Exit evidence |
|---|---|---|---|
| GFPU-500 | `ADAPT` | Bind existing text UTF/SIMD primitives to parser v2 source and error contracts. | No duplicated codec implementation. |
| GFPU-501 | `IMPLEMENT` | SIMD fused UTF/classification masks with forced ISA paths. | Scalar parity at every block boundary. |
| GFPU-502 | `IMPLEMENT` | SIMD quote/escape/comment/raw masks and state composition. | Whole-source/chunk parity. |
| GFPU-503 | `IMPLEMENT` | SIMD structural events, token boundaries, and region-map helpers. | Exact tables versus scalar. |
| GFPU-504 | `IMPLEMENT` | Task-parallel SIMD grammar VM and contiguous HIR emission. | Parsed HIR bit parity. |
| GFPU-505 | `IMPLEMENT` | ISA dispatch/evidence rows for x86, ARM, and later RISC-V vector paths. | Forced-backend CI and retained benchmark evidence. |
| GFPU-506 | `REPLACE_AFTER_GATE` | Select SIMD for measured small/medium workloads in auto mode. | >= promotion threshold including dispatch cost. |

### Phase 6 — GPU UTF, lexical, structure, token, and region stages

| ID | Status | Task | Exit evidence |
|---|---|---|---|
| GFPU-600 | `IMPLEMENT` | Backend-neutral device buffers, scan, compaction, sorting, and private staging interfaces. | CUDA/Vulkan/HIP or selected backend adapter tests; no backend types in common contracts. |
| GFPU-601 | `IMPLEMENT` | GPU UTF validation/classification and optional transcode count/emit. | Exact malformed offsets and normalized bytes versus scalar. |
| GFPU-602 | `IMPLEMENT` | GPU lexical chunk summaries and associative state composition. | Random chunking and state-table parity. |
| GFPU-603 | `IMPLEMENT` | GPU opaque masks, structural events, delimiter pairs, indentation. | Full structural table parity. |
| GFPU-604 | `IMPLEMENT` | GPU token boundary/count/emit and Unicode slow path. | Token arena parity, no text copies. |
| GFPU-605 | `IMPLEMENT` | GPU function/statement/expression/custom-block region map. | Region map parity and stable ordinals. |
| GFPU-606 | `IMPLEMENT` | Capability admission writes hard/recovery work tags before parse emit. | Deliberate bound cases compact to correct CPU queues. |

### Phase 7 — GPU local parser and direct Parsed HIR

| ID | Status | Task | Exit evidence |
|---|---|---|---|
| GFPU-700 | `IMPLEMENT` | GPU grammar count VM for declarations/statements/expressions. | Per-task counts match scalar. |
| GFPU-701 | `IMPLEMENT` | Checked global range scans over GPU and CPU-task counts. | Overflow/width tests; deterministic ranges. |
| GFPU-702 | `IMPLEMENT` | GPU action emit into token/syntax/HIR/name/constraint/tag/mapping ranges. | Exact-fill and reference validation. |
| GFPU-703 | `IMPLEMENT` | GPU local declaration/reference binding. | Local symbol parity. |
| GFPU-704 | `IMPLEMENT` | GPU type-constraint generation and post-global semantic resume. | Typed-HIR parity on supported corpus. |
| GFPU-705 | `IMPLEMENT` | Large-expression/list policy and capability tagging. | No unbounded private stack; explicit hard path. |
| GFPU-706 | `REPLACE_AFTER_GATE` | Enable hybrid GPU parser for selected valid workloads. | Zero unexpected fail/recovery, semantic parity, performance gate. |

### Phase 8 — CPU tagged task engine and ordered commit

| ID | Status | Task | Exit evidence |
|---|---|---|---|
| GFPU-800 | `IMPLEMENT` | GPU/SIMD compaction of `CPU_TODO` by class and stable order. | Queue goldens and minimal readback measurements. |
| GFPU-801 | `IMPLEMENT` | CPU hard-task count/emit using canonical scalar/SIMD programs. | Mixed CPU/GPU file parity. |
| GFPU-802 | `IMPLEMENT` | CPU recovery task processing and synthetic-node mappings. | Recovery corpus; valid path allocates no recovery structures. |
| GFPU-803 | `IMPLEMENT` | CPU global-name binder and binding-table cache. | Cross-module parity and dependency invalidation. |
| GFPU-804 | `IMPLEMENT` | Private-stage validation and ordered commit. | Late fault injection never publishes partial output. |
| GFPU-805 | `IMPLEMENT` | Reason histogram, work mapping, and plan-task telemetry. | CI can locate every unexpected hard/fail row. |
| GFPU-806 | `IMPLEMENT` | `RequireRequested` and benchmark mode reject all demotion. | No hidden fallback in performance numbers. |

### Phase 9 — Consumer parser unification

| ID | Status | Task | Exit evidence |
|---|---|---|---|
| GFPU-900 | `ADAPT` | Compiler frontend provider adapter; optionally project canonical HIR back to legacy structures initially. | Full compiler tests and stage-3 bootstrap. |
| GFPU-901 | `REPLACE_AFTER_GATE` | Compiler consumes Parsed/Typed HIR directly. | Legacy adapter no longer needed on default path. |
| GFPU-902 | `ADAPT` | Interpreter/REPL entry rules and incomplete-input session. | Compiler/interpreter HIR parity for same source/config. |
| GFPU-903 | `DELETE_AFTER_GATE` | Remove independent `lib.common.parser` Simple rule bodies and interpreter pure-parser grammar. | No dependents; compatibility APIs call shared runtime. |
| GFPU-904 | `ADAPT` | Rename current reduced “TreeSitterParser” truthfully; add native/Wasm generated Tree-sitter provider. | Provider provenance and valid corpus parity. |
| GFPU-905 | `ADAPT` | Sosh command/pipeline/redirect/script APIs consume `SoshDialect`/`ShellHir`. | Existing shell behavior tests plus new quote/substitution corpus. |
| GFPU-906 | `DELETE_AFTER_GATE` | Remove repeated shell quote/split/depth scanners. | No direct scanner dependents. |
| GFPU-907 | `ADAPT` | SDN public parser consumes `SdnDialect`; current implementation remains oracle. | SDN corpus/span/issue parity. |
| GFPU-908 | `DELETE_AFTER_GATE` | Remove duplicated SDN direct lexical scanning after parity. | One SDN lexical/structure definition. |

### Phase 10 — Homogenized cache and real incremental reuse

| ID | Status | Task | Exit evidence |
|---|---|---|---|
| GFPU-1000 | `IMPLEMENT` | Common parser cache keys, artifacts, validation, and provenance. | Cross-consumer/key golden tests. |
| GFPU-1001 | `IMPLEMENT` | Host-memory and disk CAS layers; legacy cache adapter. | Cold/warm/corrupt/stale tests. |
| GFPU-1002 | `IMPLEMENT` | GPU-resident CAS and placement metadata. | No semantic-key change across placement. |
| GFPU-1003 | `IMPLEMENT` | Lex/structure stabilization and region-level incremental planner. | Edit tests reuse unchanged segments without full reparse. |
| GFPU-1004 | `IMPLEMENT` | Native Tree-sitter old-tree session and changed-range bridge. | Edit/old-tree tests; truthful native/Wasm identity. |
| GFPU-1005 | `IMPLEMENT` | Interface/name dependency invalidation separated from parse invalidation. | Body-only edit does not discard unrelated global bindings. |
| GFPU-1006 | `IMPLEMENT` | Recovery/diagnostic cache separated from valid semantic cache. | Policy changes reuse valid lower layers only. |

### Phase 11 — Auto selection, resident mode, and production cutover

| ID | Status | Task | Exit evidence |
|---|---|---|---|
| GFPU-1100 | `IMPLEMENT` | Evidence schema and calibrated per-stage cost model. | Reproducible rows keyed by hardware/runtime/revision. |
| GFPU-1101 | `IMPLEMENT` | Auto selector includes cache/residency/transfer/sync/fallback estimates. | Decision explanation and evidence digest. |
| GFPU-1102 | `IMPLEMENT` | Resident source/index/token/region/HIR pipeline and compact CPU exchanges. | No unnecessary full-arena readback. |
| GFPU-1103 | `IMPLEMENT` | Lightweight always-on counters, dynamic aspect probes, static deep-profile build. | Three profiling modes documented and tested. |
| GFPU-1104 | `REPLACE_AFTER_GATE` | Make canonical runtime default; retain explicit legacy CPU provider. | Release gates below pass on supported platforms. |
| GFPU-1105 | `PRESERVE` | Continue CPU-only and legacy-oracle release lanes indefinitely. | No GPU dependency in CPU artifacts. |

---

## 21. Parallel workstream scheduling

Parallel implementation should begin only after Phase 1 contracts and Phase 2 stable IDs are frozen.

```text
A. Contracts/data model
   -> blocks all backend and cache hot-path work

B. Grammar inventory/generator
   -> blocks full scalar/GPU grammar execution and Tree-sitter generation

C. Legacy CPU normalization/oracle
   -> can proceed beside B after feature-ID registry is stable

D. Scalar + SIMD source/lex/structure
   -> proceeds after contracts; does not wait for all semantic actions

E. GPU primitives and lexical/structure stages
   -> proceeds after contracts/golden vectors; uses toy and extracted lex programs

F. Grammar/action VM + Parsed HIR
   -> proceeds after generator and HIR contract

G. CPU work/global/recovery engine
   -> proceeds after work/count/range contracts

H. Consumer adapters
   -> can prepare API seams early; cutover waits for scalar parity

I. Cache/incremental
   -> cache identity early; region reuse waits for stable region/state hashes

J. Test/benchmark/fault-injection
   -> active in every phase, not deferred to the end
```

Each workstream owns small commits. Generated-table changes, runtime changes, and consumer migrations should be separate commits so grammar drift and performance regressions are reviewable.

---
## 22. Verification and test plan

### 22.1 Test layers

| Layer | Purpose | Typical cadence |
|---|---|---|
| Contract/golden | Schema, IDs, serialization, count/range arithmetic, deterministic hashes | Every commit |
| Unit | One codec/mask/state/pair/token/region/grammar/action/cache operation | Every commit |
| Differential | Legacy CPU versus canonical scalar; scalar versus SIMD/GPU | Every PR for affected corpus; full in bootstrap |
| Consumer integration | Compiler, interpreter, Tree-sitter, sosh, SDN | Every PR in affected area |
| Fault injection | Device loss, queue/capacity failure, cache corruption, under/overfill | Scheduled quick subset; complete bootstrap/release |
| Fuzz/metamorphic | Random source, edits, chunking, whitespace/trivia, malformed bytes | Continuous/scheduled |
| Bootstrap | Build next compiler phase and compile full tests/tools/libs | Full bootstrap/release; selected PR lanes |
| Performance/memory | Throughput, latency, copies, allocation, residency, fallback | Baseline on relevant PRs; complete release evidence |

### 22.2 Contract and arena tests

Test:

- schema/version rejection;
- equal-length SoA columns;
- byte/token/region/HIR/reference bounds;
- stable ID registry collision prevention;
- count overflow before narrowing;
- exclusive-scan range construction;
- zero-count tasks;
- exact fill;
- deliberate underfill/overfill;
- stale snapshot/generation/digest rejection;
- nonempty input roots;
- source-backed lexeme hashing;
- backend-independent semantic roots after promotion.

### 22.3 UTF and encoding tests

Cover:

- empty input and ASCII;
- every valid UTF-8 sequence length;
- boundary code points;
- overlong forms;
- surrogate encodings;
- values above `U+10FFFF`;
- invalid/truncated continuation sequences;
- malformed bytes at every vector/block boundary;
- UTF-16 surrogate pairs and malformed pairs;
- UTF-16/32 endianness and BOM policy;
- transcode output-size count versus emit;
- original-to-UTF-8 offset checkpoint lookup;
- strict versus recovery policy;
- CPU scalar, forced SIMD ISA, and GPU byte-for-byte parity.

### 22.4 Lexical-state tests

For every possible chunk boundary, cover:

- single, double, triple, and raw strings;
- escaped and repeated backslashes;
- interpolation starts/ends and nested expressions;
- line and block comments;
- comment/string markers inside one another;
- apostrophe string/transpose contexts;
- `#` comment/attribute/hash contexts;
- `//` parallel operator versus any dialect-specific comment rule;
- raw/custom block payloads;
- Unicode adjacent to syntax bytes;
- CR, LF, and CRLF;
- state-cardinality/depth admission limits;
- chunk summary composition against a whole-source scalar run.

Property:

```text
parse(concat(chunks)) == compose_and_emit(chunks)
```

for every tested chunk partition.

### 22.5 Structural tests

Cover:

- nested and sibling `()[]{}`;
- mixed delimiter types;
- `([)]`, missing opener, missing closer;
- delimiter bytes inside opaque regions;
- `<<< >>>`;
- custom blocks and nested dialect blocks;
- empty blocks;
- maximum configured depth and one beyond;
- indentation increases, same-level lines, multi-dedent, blank/comment-only lines;
- tabs/spaces policy;
- nearest-lower-indent parent and block end;
- stable pair/region ordinals under different worker scheduling.

### 22.6 Token and region tests

Cover every canonical token and grammar feature, including:

- longest-match operators;
- identifiers, keyword boundaries, and underscore forms;
- Unicode XID start/continue;
- integer/float/base/exponent forms;
- string/raw/triple/interpolation tokens;
- array suffixes and collection/custom literal prefixes;
- indentation tokens;
- function/type/trait/impl/module/import regions;
- control-flow statement regions;
- expression precedence and associativity;
- body/parameter/call/index/member regions;
- custom blocks;
- false region hints rejected by grammar without corrupting neighboring tasks.

### 22.7 Grammar and HIR differential tests

For every valid corpus item:

```text
LegacyCpu normalized result
    == CanonicalScalar
    == CanonicalSIMD
    == GPU/hybrid
```

Compare:

- acceptance;
- token kinds/spans/lexeme digests;
- feature IDs;
- source mappings;
- Parsed HIR kind/edge/operand/name/type-variable columns;
- local bindings;
- global-name work and binding results;
- type constraints and Typed HIR;
- demanded tags/indexes;
- semantic artifact root.

When legacy AST shape is intentionally different, compare normalized feature/HIR semantics rather than private node indices.

### 22.8 CPU work-table tests

Construct files that produce mixtures of:

- GPU-ready declarations;
- known-hard long expressions;
- dialect CPU hooks;
- malformed/recovery regions;
- global-name rows;
- transient GPU count failure;
- late kernel/device failure;
- capacity overflow.

Assert:

- correct tags and reasons;
- compact CPU queue contains exactly the expected tasks;
- stable class/range/order;
- CPU handlers use mapped slices, not full-file rescan;
- combined counts produce deterministic global ranges;
- GPU/CPU mixed emission equals all-CPU output;
- late failure discards staging output;
- `RequireRequested` never demotes;
- runtime `HARD`/`FAIL` histograms match the work rows.

Example expected table:

```text
id  stage          region  tags                         reason                       handler
10  ParseStmt      18      GPU_DONE                     None                         -
11  ParseExpr      19      CPU_TODO|HARD                LongExpressionPolicy         CanonicalSimdProgram
12  ErrorRecovery  20      CPU_TODO|RECOVERY            UnterminatedString           RecoveryProgram
13  GlobalName     21      CPU_TODO|GLOBAL_NAME         DesignGlobalName             GlobalNameBinder
14  ParseDecl      22      CPU_TODO|FAIL|RETRYABLE      KernelExecutionFailed        CanonicalScalarProgram
```

### 22.9 Error recovery tests

Recovery is CPU-owned but must integrate with GPU-produced mappings:

- invalid token runs;
- missing/extra delimiters;
- bad indentation;
- unterminated strings/comments/interpolation;
- incomplete REPL entries;
- malformed custom block boundaries;
- multiple errors with guaranteed progress;
- bounded diagnostics and synthetic-node counts;
- source anchoring through non-UTF-8 normalization;
- recovered/synthetic flags never enter valid-cache namespace;
- valid regions before/after an error are preserved where the recovery contract permits.

### 22.10 Global-name tests

Cover:

- module/import/export paths;
- aliases and qualification;
- visibility;
- duplicate global declarations;
- overload candidate sets;
- types/traits/impls and associated members;
- cyclic modules;
- incremental interface hash changes;
- body-only changes that should not invalidate unrelated bindings;
- deterministic ambiguity/unresolved ordering;
- CPU result applied back to GPU semantic continuation.

### 22.11 Tree-sitter tests

- `tree-sitter generate` is clean and reproducible;
- generated parser/scanner/node-types carry the current grammar digest manifest;
- every visible rule has corpus coverage;
- valid Simple corpus is accepted by both canonical parser and native/Wasm Tree-sitter;
- canonical feature/node mapping covers every stable visible node;
- incomplete/malformed cases satisfy Tree-sitter-specific expected trees;
- old tree is edited before incremental parse;
- changed ranges feed shared invalidation;
- provider provenance distinguishes native, Wasm, and fallback paths;
- no current reduced parser can report native Tree-sitter identity.

### 22.12 Interpreter tests

- expression/statement/module entry rules equal compiler parsing for the same source/config;
- REPL “complete”, “needs more input”, and “invalid” states;
- append/session behavior without global-state leakage;
- cached Parsed/Typed HIR reuse across compiler/interpreter when identities match;
- execution semantics unchanged after parser migration.

### 22.13 sosh tests

- words under unquoted/single/double/raw contexts;
- escapes and line continuation;
- variables, command substitution, nested substitutions;
- pipelines, parallel/boolean composition, background execution;
- attached and separated redirections, file descriptors, append/input;
- functions, `if`, loops, `case`;
- comments only in valid shell contexts;
- script and direct command use the same token/grammar rules;
- parse output separates expansion/execution from syntax;
- tiny interactive commands select scalar/SIMD unless evidence justifies GPU.

### 22.14 SDN tests

- scalar values, dictionaries, arrays, nested values;
- quoted strings/escapes/comments;
- commas, colons, newlines, and indentation forms;
- source spans and issue records;
- duplicate keys under configured policy;
- malformed/incomplete recovery;
- old public API result parity;
- scalar/SIMD/GPU dialect parity;
- SDN grammar-table bootstrap reproducibility.

### 22.15 Fuzzing and metamorphic tests

Run grammar-aware and byte-level fuzzers against:

- legacy CPU;
- canonical scalar;
- each forced SIMD ISA;
- GPU count and emit;
- native Tree-sitter;
- incremental edit sequences;
- cache serialize/restore.

Metamorphic transformations include:

- legal whitespace/trivia changes;
- equivalent line endings under policy;
- identifier/string Unicode boundary placement;
- source split into every chunk-size/offset combination;
- declaration/function order where semantics permit;
- cache cold/warm runs;
- CPU/GPU task partition changes;
- device staging versus resident placement.

### 22.16 Bootstrap and whole-repository tests

The release lane must:

1. build the current/seed compiler;
2. build the next-phase compiler;
3. use that compiler to build the following phase;
4. compile the full Simple test corpus, important tools, libraries, interpreter, shell, and SDN stack;
5. compare stage outputs under forced legacy CPU, canonical scalar, SIMD, and supported GPU modes;
6. rerun affected earlier phases if a later compiler changes relevant frontend artifacts;
7. execute on a CPU-only environment with no GPU libraries/device.

A parser change is not complete when only parser unit tests pass.

---

## 23. Performance and memory evaluation

### 23.1 Required metrics

Per stage and end to end:

- input bytes/s and files/s;
- UTF scalars/s and transcode expansion ratio;
- tokens/s;
- structural events and pairs/s;
- regions/s;
- Parsed/Typed HIR nodes/s;
- host CPU time, GPU time, transfer time, synchronization time;
- device queue wait;
- source/token/HIR copies and bytes copied;
- allocations and peak host/device memory;
- cache hit by layer;
- incremental bytes/regions reparsed;
- CPU task count/bytes by `HARD`, `FAIL`, `RECOVERY`, `GLOBAL_NAME`;
- GPU occupancy/divergence and per-region stack/scratch usage;
- end-to-end compiler/interpreter/shell startup latency.

### 23.2 Benchmark matrix

Use:

- tiny REPL expressions and one-line shell commands;
- small ordinary source files;
- medium generated files;
- large single files;
- many-file project batches;
- Unicode-heavy and ASCII-heavy corpora;
- custom-block-heavy source;
- valid versus malformed/incomplete corpora;
- cold source/cache, warm normalized source, warm token/region cache, warm HIR cache;
- staged versus resident data;
- CPU-only, forced scalar, forced ISA, forced GPU, auto;
- integrated compiler bootstrap, interpreter startup/script, sosh script, and SDN workloads.

### 23.3 Promotion rules

A stage/backend becomes selectable by default only when:

- semantic parity passes on the required corpus;
- malformed-input and fault-injection tests pass;
- no silent fallback occurs in the benchmark;
- benchmark identity matches runtime/dialect/grammar/binary/source revision;
- median end-to-end stage speedup meets the configured gate, initially `>= 1.5x` over its baseline;
- p95 latency and peak memory remain within declared budgets;
- speedup includes transfer, synchronization, CPU task drain, and validation;
- evidence rows and digest are retained.

A faster kernel with slower total parsing is not promoted.

### 23.4 Expected dispatch tendency, not a fixed policy

| Workload | Likely best path |
|---|---|
| One tiny REPL/shell line | Scalar CPU |
| Small source with existing SIMD-capable CPU | SIMD CPU |
| Many independent files already batched | SIMD multicore or GPU, selected by evidence |
| One large valid source | GPU structural/token/region; GPU local parse if region parallelism is sufficient |
| Source/IR already resident on GPU | Resident GPU except compact CPU global-name/recovery exchanges |
| Malformed editor buffer | Native Tree-sitter for CST plus CPU recovery where canonical semantics are requested |
| High hard-task ratio | Canonical CPU until capability coverage improves |

### 23.5 Memory rules

- Source is immutable and shared; no per-token text copies.
- Dense bitmaps are retained only when demanded or useful; compact structural positions may replace them downstream.
- SoA arrays use the narrowest verified index width per artifact, with checked promotion to wider storage when necessary.
- Count passes determine exact output capacity.
- GPU private stacks/scratch are bounded by manifests; outliers become hard tasks.
- CPU task readback is compact; resident mode does not copy complete arenas for a few tasks.
- `TagDemand.Off` means zero tag/index allocation/work.
- Recovery structures are absent on the valid strict path.
- Cache placement and eviction account for recomputation cost, dependency fanout, and residency—not only byte size.

### 23.6 Profiling modes

1. **Always-on lightweight:** stage durations, bytes/items, cache hits, backend, task counts/reasons, peak ranges. Low enough overhead for normal builds.
2. **Dynamic aspect probes:** per-kernel/per-rule/per-action timing, queue and allocation events, selected without recompiling when overhead is acceptable.
3. **Static deep profile:** recompiled instrumentation for lane divergence, memory transactions, detailed state/action counts, full oracle mapping, and hardware counters.

A profiling mode must be recorded in evidence identity and must not contaminate ordinary cache keys.

---

## 24. Acceptance and release gates

### 24.1 Architecture gate

- v2 contracts and stable ID registries are frozen and versioned.
- Common contracts contain no CUDA/Vulkan/HIP/private backend handles.
- One generated canonical Simple grammar exists.
- Original full CPU frontend remains runnable and independent.
- Parser provider, execution backend, and offload mode are separate typed concepts.

### 24.2 Correctness gate

- Full valid Simple corpus has normalized semantic parity among legacy CPU, canonical scalar, forced SIMD, and supported GPU paths.
- Compiler and interpreter produce the same Parsed/Typed HIR for matching entry/config profiles.
- CPU global-name binding is deterministic and equivalent across upstream backend partitions.
- CPU recovery is bounded, deterministic, source-mapped, and absent from valid strict builds.
- sosh and SDN public behavior passes migration parity suites.
- Native/Wasm Tree-sitter accepts the valid canonical corpus and satisfies its separate invalid-source corpus.

### 24.3 Work-table gate

- Every non-GPU region has a stable reason and CPU handler.
- No valid-source production corpus row has `FAIL`.
- `RECOVERY` appears only for malformed/incomplete input.
- `GLOBAL_NAME` is reported separately from fallback.
- Unexpected `HARD` rows fail GPU-completeness CI after the corresponding capability is promoted.
- Late failure never publishes partial output.
- CPU can locate every task from mappings without full-file reparsing unless full-stage fallback is explicitly selected.

### 24.4 Cache gate

- Source, grammar, provider, runtime, output, feature, and recovery identities are complete.
- Backend-independent reuse occurs only after parity certification.
- Stale/corrupt/foreign cache entries fail closed.
- Region edits reuse unchanged artifacts after lexical/structural stabilization.
- Tree-sitter old-tree reuse follows exact edit lineage.
- Global-name/interface invalidation does not unnecessarily invalidate lexical/parse layers.

### 24.5 Performance gate

- Promoted stages meet the evidence threshold including all overhead.
- Auto mode does not choose GPU for measured losing workloads.
- CPU scalar/SIMD paths do not regress outside the allowed budget.
- Peak host/device memory and output over-allocation remain within manifests.
- CPU fallback/task ratio is visible and budgeted.
- No performance report includes silent demotion.

### 24.6 Compatibility and rollback gate

- `--frontend=legacy-cpu` remains functional.
- CPU-only builds contain no mandatory GPU runtime initialization/dependency.
- Existing compiler, interpreter, shell, and SDN APIs remain available through adapters during migration.
- Every phase can disable the new provider at session/config level without reverting unrelated code.
- Duplicate parser/scanner code is deleted only after all reverse dependencies and rollback tests pass.

---

## 25. Risk register

| Risk | Effect | Mitigation |
|---|---|---|
| Canonical grammar extraction changes language behavior | Bootstrap or user-source regression | Feature inventory, generated coverage matrix, legacy differential oracle, small feature-by-feature extraction. |
| Original one-pass parser bugs become encoded in tables | Fast but wrong shared behavior | Treat legacy behavior as evidence, not unquestionable specification; fix bugs with focused corpus and explicit grammar decision. |
| Common-mode generated-runtime defect | Scalar/SIMD/GPU all agree incorrectly | Preserve independently implemented legacy full CPU path and native Tree-sitter valid-source cross-check. |
| GPU launch/transfer overhead exceeds work | Slower normal builds | Evidence-based per-stage auto selection; batch/resident paths; scalar/SIMD first class. |
| Dynamic/custom lexical features create unbounded state | GPU state explosion | Bounded capability manifests; nested dialect requests; hard CPU tasks; language rules favor locally decidable syntax. |
| Indentation or expression outliers require large stacks | Occupancy/memory collapse | Region bounds, nearest-smaller structural algorithms, per-task stack manifests, long-region policies and CPU handler. |
| Late GPU failure corrupts mixed output | Nondeterministic or unsafe compiler result | Private staging, exact fill/reference validation, discard-and-rerun stage, no partial publish. |
| CPU task queue becomes hidden normal path | Claimed offload without real coverage | Separate reason metrics, valid-corpus hard/fail budgets, benchmark `RequireRequested`, capability report. |
| Tree-sitter grammar diverges | Editor/compiler disagree | Generated projection, common digest/corpus, explicit narrow overlay, valid-source parity CI. |
| SDN grammar format creates bootstrap cycle | Build cannot regenerate itself | Check in generated tables; seed compiler consumes generated artifacts; regeneration is a development/full-bootstrap step. |
| Cache key misses semantic input | Stale incorrect result | Layered explicit identities, nonempty roots, dependency/interface hashes, negative mutation tests. |
| Overly broad cache invalidation erases gains | Slow incremental builds | Separate raw/text/lex/region/HIR/global/recovery IDs and mappings. |
| Overly narrow invalidation reuses stale context | Wrong parse/binding | Entry/exit state hashes, parent-context digest, old-to-new mappings, oracle sampling. |
| Parser refactor broadens compiler rebuild scope | Slow development | Stable common contracts, generated immutable tables, adapters, small commits, targeted quick tests. |
| HIR direct path breaks tooling that expects AST | Tool regression | Optional SyntaxArena; Parsed-HIR-to-legacy adapter during migration; output-profile-specific caches. |
| Vendor backend semantics differ | Cross-platform divergence | Backend-neutral integer contracts, forced backend tests, scalar oracle, no floating-point scan semantics in parsing. |
| Error diagnostics differ across modes | User-visible instability | CPU diagnostic/recovery arbitration and stable fact IDs; GPU emits facts/mappings, not final localized text. |

---

## 26. Recommended configuration surface

Conceptual SDN configuration:

```sdn
parser:
  provider: simple-canonical
  mode: auto
  fallback: allow-region-cpu
  deterministic: true
  oracle:
    provider: simple-legacy-cpu
    policy: sampled
  outputs:
    syntax: false
    parsed_hir: true
    typed_hir: true
    tags: demanded
  cache:
    memory: true
    disk: true
    resident_gpu: auto
  recovery:
    policy: strict
```

Suggested diagnostic/development controls:

```text
--frontend=legacy-cpu|canonical
--parse-mode=cpu-reference|hybrid-vector-gpu|resident-gpu|auto
--parse-force-backend=scalar|simd|gpu
--parse-fallback=allow-region-cpu|allow-full-cpu|require-requested
--parse-oracle=off|sampled|full
--parse-dump-regions=<path>
--parse-dump-work=<path>
--parse-dump-capabilities=<path>
--parse-explain-dispatch
--parse-cache=off|memory|disk|resident
--parse-recovery=strict|recover|interactive
```

These are proposed names; integrate with the repository’s established config/CLI naming conventions rather than adding duplicate option parsers.

---

## 27. Developer capability and TODO reports

Add generated/runtime reports so missing offload work is discoverable without reading logs manually.

### 27.1 Static capability report

Conceptual command:

```text
simple parser-capability report \
  --dialect simple \
  --backend gpu \
  --status hard,unimplemented,experimental
```

Output:

```text
Capability  Feature                 Rule/action       Status         CPU handler       Plan task
0x0142      raw-string-hash-depth   lex.raw_string    HARD_CPU       CanonicalScalar   GFPU-602
0x0810      very-long-expression    expr.precedence   EXPERIMENTAL   CanonicalSimd     GFPU-705
```

### 27.2 Runtime work report

```text
simple parser-work report build/work_table.sdn --todo-only
```

Output groups by:

- reason;
- grammar feature/capability;
- file/module;
- stage;
- total bytes/HIR nodes;
- CPU handler;
- first and largest source region;
- retry/fatal state;
- implementation-plan task ID.

### 27.3 CI budgets

Examples:

```text
valid bootstrap corpus:
  fail_tasks == 0
  recovery_tasks == 0
  missing_handler_tasks == 0

GPU-complete feature set:
  hard_tasks[unexpected] == 0

performance lane:
  total_fallback_tasks == 0 unless benchmark explicitly targets fallback
```

This turns “GPU support” into measurable grammar/action coverage rather than a mode name.

---

## 28. Final architecture rules

1. The existing full CPU parser remains available permanently as `SimpleLegacyCpu` and is exercised in release CI.
2. The canonical runtime has scalar, SIMD, and GPU executors over identical versioned tables and arenas.
3. GPU handles the valid-source frontend through Parsed HIR, local binding, constraints, and post-global semantic continuation.
4. CPU owns global name resolution and syntax error recovery.
5. Known-hard work is tagged before global output reservation and counted/emitted by CPU into deterministic ranges.
6. Late GPU execution/invariant failures discard private stage output; they are never patched into a supposedly valid artifact.
7. Function/statement/expression mapping is structural indexing, not parsing.
8. Direct Parsed HIR is the compiler fast path; AST/CST is optional output or the legacy oracle representation.
9. Simple compiler and interpreter use one canonical Simple grammar and HIR.
10. SDN and sosh use the same runtime but their own dialects and output sinks.
11. Native/Wasm Tree-sitter is generated from the canonical Simple grammar, retains its own incremental/recovery runtime, and is never the compiler semantic authority.
12. The current reduced Simple-coded “TreeSitterParser” must be renamed truthfully and removed after native/canonical adapters are complete.
13. All generated grammar artifacts carry one grammar digest and are checked for clean regeneration.
14. Valid-source parity is exact; invalid-source recovery contracts are provider-specific but bounded and deterministic.
15. Cache keys describe semantics, grammar, source, provider, output, and recovery policy—not merely file path or selected hardware.
16. Backend provenance is recorded in receipts; backend is omitted from certified semantic cache keys.
17. Preprocessing preserves source mappings through active masks/regions rather than untracked text rewriting.
18. Every unsupported or failed capability is visible in static and runtime mapping tables with a stable reason and CPU handler.
19. No GPU/SIMD path is promoted without parity, fault tests, retained evidence, and measured end-to-end speedup.
20. No parser/scanner duplicate is deleted before reverse dependencies, bootstrap, rollback, and behavior parity are proven.

---

## 29. Research and repository references

### Repository baseline and current implementation

- [Repository baseline commit](https://github.com/ormastes/simple/tree/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae)
- [Compiler parser](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/src/compiler/10.frontend/core/parser.spl)
- [Compiler core frontend runner](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/src/compiler/10.frontend/core/frontend.spl)
- [Frontend parse cache](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/src/compiler/10.frontend/frontend_parse_cache.spl)
- [Current HIR lowering](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/src/compiler/10.frontend/core/hir/lowering.spl)
- [Parser framework Wave-1 types](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/src/lib/common/structural/parse/parse_types.spl)
- [CPU-reference lexical executor](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/src/lib/common/structural/parse/parse_cpu_reference.spl)
- [v2-oriented parser contracts seam](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/src/lib/common/structural/parse/contracts.spl)
- [Dialect compatibility seam](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/src/lib/common/structural/parse/dialect.spl)
- [Output range planning](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/src/lib/common/structural/parse/output_plan.spl)
- [Parallel lex stub](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/src/lib/nogc_async_mut/structural/parse/parallel_lex.spl)
- [Structural index stub](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/src/lib/nogc_async_mut/structural/parse/structural_index.spl)
- [Incremental planner stub](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/src/lib/nogc_async_mut/structural/parse/incremental.spl)
- [Auto profile stub](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/src/lib/nogc_async_mut/structural/parse/auto_profile.spl)
- [Parser framework unit tests](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/test/01_unit/lib/structural/parse/parse_cpu_reference_spec.spl)
- [Parser framework system tests](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/test/03_system/app/compiler/feature/parser_framework_spec.spl)
- [Interpreter Tree-sitter-wrapper parser](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/src/app/interpreter/parser.spl)
- [Interpreter pure-parser wrapper](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/src/app/interpreter/parser_pure.spl)
- [Simplified common parser](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/src/lib/common/parser/parser.spl)
- [Current Simple-coded “TreeSitterParser” implementation](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/src/compiler_rust/lib/std/src/parser/treesitter/__init__.spl)
- [sosh pipeline parser](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/src/os/apps/shell/shell_pipe.spl)
- [sosh redirect parser](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/src/os/apps/shell/shell_redirect.spl)
- [sosh script parser](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/src/os/apps/shell/shell_script.spl)
- [SDN lexer](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/src/lib/common/sdn/lexer.spl)
- [SDN parser](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/src/lib/common/sdn/parser.spl)
- [Existing parser framework design](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/doc/05_design/parser_framework.md)
- [Existing compiler-offload architecture](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/doc/04_architecture/simple_compiler_offload.md)
- [Existing compiler-offload detail design](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/doc/05_design/simple_compiler_offload.md)
- [UTF-8 internationalized text architecture](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/doc/01_research/lib/text_i18n/simple_utf8_internationalized_text_architecture_2026-08-25.md)
- [SIMD UTF/text optimization plan](https://github.com/ormastes/simple/blob/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae/doc/03_plan/compiler/simd_opt/simd_utf8_text_api_optimization.md)

### External primary sources and implementations

- [simdutf](https://github.com/simdutf/simdutf) — SIMD UTF validation/transcoding and runtime implementation selection.
- [simdjson design notes](https://github.com/simdjson/simdjson/blob/master/HACKING.md) — separation of UTF/string/structural discovery from later representation construction.
- [ParPaRaw: Massively Parallel Parsing of Delimiter-Separated Raw Data](https://arxiv.org/abs/1905.13415) — GPU finite-state context composition without an initial sequential context pass.
- [NVIDIA CUB DeviceScan](https://nvidia.github.io/cccl/unstable/cub/api/structcub_1_1DeviceScan.html) and [DeviceSegmentedScan](https://nvidia.github.io/cccl/unstable/cub/api/structcub_1_1DeviceSegmentedScan.html) — device-wide associative scan contracts.
- [Pison](https://github.com/AutomataLab/Pison) — parallel structural-index construction and leveled bitmaps.
- [cuJSON](https://github.com/AutomataLab/cuJSON) — GPU UTF validation, tokenization, nesting recognition, and matching-pair/structural output arrays.
- [Pareas](https://github.com/Snektron/pareas) — research implementation of a GPU-accelerated compiler and parallel lexer/parser generator.
- [Associative Operator Precedence Parsing](https://doi.org/10.1145/3578178.3578233) — locally parsable/associative parsing techniques for exposing parallelism.
- [Tree-sitter introduction](https://tree-sitter.github.io/) — parser-generator and incremental/error-tolerant design goals.
- [Tree-sitter grammar generation](https://tree-sitter.github.io/tree-sitter/cli/generate.html) — `grammar.js`/`grammar.json` to generated parser artifacts.
- [Tree-sitter incremental editing](https://tree-sitter.github.io/tree-sitter/using-parsers/3-advanced-parsing.html) — edit the old tree and pass it to the next parse for structure reuse.
- [Tree-sitter corpus tests](https://tree-sitter.github.io/tree-sitter/creating-parsers/5-writing-tests.html) — per-rule grammar corpus methodology.

---

## 30. Bottom line

Simple’s one-pass semantics and existing flat-arena/MDSOC+ direction make a GPU frontend credible, provided the implementation is **structural and table-driven rather than a line-for-line CUDA rewrite of recursive descent**.

The correct target is:

```text
one source snapshot
+ one canonical grammar
+ one scalar/SIMD/GPU data model
+ one explicit CPU work table
+ direct Parsed HIR
+ CPU global names and recovery
+ one layered cache protocol
+ an independent permanent legacy CPU oracle
```

The first implementation milestone is not a GPU kernel. It is eliminating grammar/identity ambiguity, freezing v2 tables, normalizing the original CPU oracle, and making every hard/failure path explicit. Once those contracts exist, SIMD and GPU work can proceed in parallel without creating another parser fork.
