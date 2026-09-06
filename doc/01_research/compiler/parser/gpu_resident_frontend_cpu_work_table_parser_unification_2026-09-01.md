# Simple GPU-Resident Frontend, CPU Work Table, SIMD, and Parser-Unification Design

**Status:** Proposed architecture and staged implementation plan  
**Date:** 2026-09-01  
**Repository baseline:** `ormastes/simple@1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae`  
**Proposed repository location:** `doc/05_design/compiler/frontend/gpu_offload_cpu_work_table_parser_unification_2026-09-01.md`  
**Supersedes/extends:** the parser and tagged-structural portions of `simple_mdsoc_tagged_structural_gpu_architecture_2026-07-31.md`

---

## 1. Executive decision

Simple should target an end-to-end GPU frontend in which the GPU performs all normal, valid-source work from source normalization through parsed HIR and local semantic processing. Two operations remain mandatory CPU authority in the first production design:

1. **Global name resolution**, including module/import/visibility graph authority and deterministic global symbol identity.
2. **Syntax error recovery**, including synchronization, insertion/skipping policy, partial-tree repair, and final diagnostic arbitration.

The intended normal path is therefore:

```text
source bytes
  -> encoding normalization / UTF-8
  -> UTF-8 validation + byte classification
  -> lexical-state and opaque-region map
  -> delimiter + indentation structure
  -> tokens
  -> function/statement/expression unit map
  -> local parse
  -> Parsed HIR
  -> local scopes, local names, local constraints
  -> CPU global-name request batch
  -> CPU global-name patch
  -> GPU type/trait/effect/DI/AOP/desugar/MIR continuation
  -> output
```

Malformed input takes an explicit side path:

```text
GPU detects a lexical/structural/grammar failure
  -> emits a tagged CpuWorkItem
  -> CPU reference parser/recovery processes the smallest safe unit
  -> CPU emits a recovery/diagnostic patch
  -> result is merged deterministically
```

This design has five non-negotiable properties:

- The **complete scalar CPU parser remains available forever** as the executable correctness oracle, bootstrap path, debugging path, and independent fallback.
- A **CPU SIMD mode** accelerates normalization, UTF-8 validation, byte classification, structural indexing, and token creation while retaining the same CPU parser and semantics.
- GPU limitations and failures are never hidden. Every deferred operation becomes a **queryable, persistent, tagged work-table row**.
- Compiler, interpreter, editor/Tree-sitter integration, shell, and SDN use one **shared parsing runtime and contracts**, but use separate dialect grammars where their languages genuinely differ.
- Grammar acceptance cannot silently diverge. A grammar feature must be represented in a canonical manifest and checked against every parser surface and generated artifact.

### 1.1 What “whole GPU offload” means here

“Whole” does not mean that the CPU cannot launch kernels, perform file I/O, format diagnostics, or write an object file. It means that valid-source frontend and semantic computation is not duplicated on the CPU merely because the input is source text.

The target GPU-resident lane includes:

- UTF-8/UTF-16/UTF-32/Latin-1 normalization where explicitly selected;
- UTF-8 validation;
- byte and code-point classification;
- strings/comments/raw-block recognition;
- delimiter and indentation maps;
- tokenization;
- declaration/function/statement/expression maps;
- deterministic local parsing;
- direct Parsed-HIR emission;
- local scope and local-name resolution;
- global-name request extraction;
- application of CPU-produced global-name patches;
- type-constraint generation and solving;
- overload/trait selection after global candidate sets are available;
- effect/capability checks that do not require error recovery;
- DI/AOP metadata processing;
- desugaring and later GPU-capable compiler stages.

The CPU is authoritative for the two deliberately excluded operations. Temporary compatibility spills are allowed during migration, but they must be tagged and ratcheted toward zero.

### 1.2 HIR is not the hard boundary

Parsed-HIR construction is not inherently difficult on a GPU. A local parser can directly emit HIR with symbolic references:

```text
foo(x + 1)
```

can become:

```text
Call(
    callee = UnresolvedName(hash("foo")),
    args = [
        Add(
            Ref(UnresolvedName(hash("x"))),
            IntLiteral(1)
        )
    ]
)
```

The difficult global operation is deciding which globally visible `foo` and `x` those symbols denote. The CPU global-name service returns stable symbol IDs or candidate sets; the GPU then patches and continues.

The production frontend therefore does not require a pointer-rich AST between tokens and HIR. An AST/CST view remains available through adapters for compatibility, diagnostics, tooling, and differential testing.

---

## 2. Scope

This document covers a shared architecture and migration plan for:

- the Simple compiler frontend;
- the Simple interpreter parser;
- the current Simple “TreeSitter”/outline and partial-parser facilities;
- a real native Tree-sitter grammar and incremental editor integration;
- the SimpleOS shell parser, including commands, quotes, pipelines, redirects, and script control flow;
- the Simple Data Notation parser in both Simple and Rust/bootstrap implementations;
- scalar CPU, CPU SIMD, GPU hybrid, GPU verification, and GPU-resident execution modes;
- grammar generation, divergence checks, differential tests, and release gates.

The document defines interfaces to later HIR/MIR/backend stages but does not prescribe a replacement for every existing backend implementation in one change. The frontend migration must be independently deployable and reversible.

---

## 3. Non-goals

This work must not:

- delete or weaken the current complete CPU parser;
- require a GPU to bootstrap Simple;
- make the editor parser the compiler’s language authority;
- force Simple, shell, and SDN into one grammar;
- make every tiny REPL line pay GPU launch and transfer overhead;
- guess arbitrary legacy source encodings from byte statistics;
- silently accept syntax in one parser that another parser rejects;
- silently fall back from GPU to CPU;
- replace stable diagnostics with nondeterministic “first GPU thread to report” behavior;
- introduce a common-mode failure by generating the independent CPU reference parser from exactly the same action program as the GPU parser;
- perform a repository-wide parser rewrite before parity and rollback infrastructure exists.

---

## 4. Current repository audit

The following observations are based on `main` at commit
`1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae`.

### 4.1 Compiler parser and lexer

| Surface | Current observation | Architectural consequence |
|---|---|---|
| `src/compiler/10.frontend/core/parser.spl` | Recursive-descent parsing is split into expression, statement, and declaration modules, but active state is held in module-level globals. The file explicitly notes that this arrangement works when compiled to C and not in the interpreter because of a closure/state issue. | Introduce a reentrant `ParserContext`, but only behind an adapter and parity gate. The current implementation becomes `CpuReferenceParser`. |
| `src/compiler/10.frontend/core/lexer.spl` | The lexer also carries substantial module/global state and compatibility state. Its history documents byte-versus-code-point indexing failures and environment/module mirrors. | Canonical offsets must become UTF-8 byte offsets with an explicit origin map. Lexer state must be per snapshot, not hidden process state. |
| `src/compiler/10.frontend/flat_ast_bridge.spl` | The compiler already converts a flat, index-based core AST into the richer frontend module shape expected by HIR lowering. | This is a useful compatibility boundary. Add a `ParsedHirAdapter` alongside it rather than replacing all consumers at once. |
| `src/compiler/10.frontend/parser_factory.spl` | A second parser abstraction owns source, tokens, errors, outline, and resolved blocks. | Fold this responsibility into one `ParserService`; do not retain two public parser lifecycle models. |
| `src/compiler/10.frontend/parser_types*.spl` | The rich AST contains declarations, functions, contracts, attributes, domain blocks, DI/AOP-related data, and many language-specific fields. | The direct-HIR lane needs an explicit field/action coverage matrix before bypassing this AST. |

### 4.2 Outline, partial parsing, and “TreeSitter”

The repository currently contains a sizeable handwritten outline parser under
`src/compiler/10.frontend/treesitter/`. It consumes the core lexer and independently dispatches attributes, imports, functions, classes, structs, enums, traits, impls, constants, and other declarations. It also owns synchronization and error production.

`src/compiler/10.frontend/treesitter.spl` describes a Tree-sitter-style outline facility, but a code search at this baseline did not find a native Simple `grammar.js` or a `tree_sitter_simple` generated language symbol. The current subsystem should therefore be treated as a **handwritten outline parser**, not as the native Tree-sitter parser.

There is also an indentation-based heuristic partial parser under
`src/compiler/10.frontend/parser/partial.spl`, and a separate recovery subsystem under
`src/compiler/10.frontend/parser/recovery.spl`.

Consequences:

- Rename the current implementation to `LegacyOutlineParser` or `SimpleOutlineParser` immediately. Names must not imply native Tree-sitter behavior that is not present.
- Do not maintain the outline parser as an independent grammar.
- Generate or project outline records from the canonical grammar/CST/region map.
- Keep the current partial/recovery parser as CPU compatibility code until a shared recovery API reaches parity.
- Add a real `tree-sitter-simple` grammar generated from or checked against the canonical grammar manifest.

### 4.3 Interpreter

`src/app/interpreter/parser_pure.spl` uses a parser module named
`lib.parser.parser` and exposes module, statement, and expression entry points.
A February 2026 report records an earlier parser-unification phase that moved an interpreter/SMF parser into `src/lib/parser/`.

At the audited commit, a direct contents lookup for `src/lib/parser/parser.spl` did not resolve. That may reflect path generation, a moved module, or stale documentation/imports; it must be verified by the actual build and module resolver before any deletion is attempted.

The important architectural conclusion is independent of that path question:
the interpreter must stop owning a grammar fork. It should call the shared
`ParserService` with an interpreter-appropriate output adapter.

### 4.4 SimpleOS shell

The shell currently divides parsing among independent scanners:

- `shell_script.spl` manually splits lines and whitespace and recognizes
  `if/elif/else/fi`, `while/done`, `for/done`, `case/esac`, function definitions,
  assignments, and other statements.
- `shell_pipe.spl` independently scans quotes and backslashes to split `|`, then
  contains another simple word splitter.
- `shell_redirect.spl` separately interprets redirect and background tokens.

This creates multiple definitions of quote, escape, word, and operator behavior. It is a high-risk divergence point.

The shell needs one `ShellDialect` and one lossless shell token/word representation.
Pipeline, redirect, background, expansion, and control-flow parsing must consume that
shared representation.

### 4.5 SDN

The Simple SDN implementation and Rust/bootstrap SDN implementation differ substantially:

- `src/lib/common/sdn/lexer.spl` has a small token set and no span-bearing token structure.
- `src/lib/common/sdn/parser.spl` performs much parsing by direct string and line scanning; it separately computes spans and issues.
- `src/compiler_rust/sdn/src/lexer.rs` has typed literals, identifiers, table tokens, punctuation, indentation, bracket-depth handling, comments, and source spans.
- `src/compiler_rust/sdn/src/parser.rs` describes itself as a one-pass LL(2) parser and currently performs handler replay after building a value.

These implementations must be reconciled against one canonical `SdnDialect` and a shared corpus. The Rust parser remains the bootstrap oracle until the generated/shared path proves parity.

### 4.6 Existing SIMD base

The repository already exposes runtime SIMD text calls through
`src/lib/encoding/simd_text_sffi.spl`, including ASCII detection, UTF-8 validation,
code-point counting, string search, and ASCII case conversion.

`src/runtime/runtime_simd_utf8.c` already contains scalar, SSE2, AVX2, and NEON code paths. The current AVX2 validation strategy fast-skips all-ASCII vectors and uses scalar validation for non-ASCII regions. This is a useful base, but it does not yet produce the structural masks required by a parser frontend.

The new SIMD parser lane should extend this dispatch infrastructure rather than create an unrelated SIMD subsystem.

### 4.7 Generated grammar inventory

`spec/compiler_schema/registry/compiler.frontend.Grammar.sdn` is a generated inventory of productions and tags found in compiler source. It is useful for coverage and documentation, but it is not yet a normative grammar and does not cover all parser surfaces.

The future grammar manifest should generate this inventory, not be inferred only from whichever parser implementation happened to be scanned.

### 4.8 Existing parity-gate precedent

The baseline repository recently added a gate comparing three duplicated C-runtime source rosters after one roster silently drifted. Parser and grammar surfaces have the same failure shape: multiple lists or implementations can drift while each remains locally plausible. The parser program should adopt the same policy:

> duplicated grammar surfaces require an explicit parity inventory and a push gate.

---

## 5. Required invariants

### I-01 — CPU reference permanence

A complete scalar CPU path must parse and compile every supported Simple feature without GPU or SIMD requirements. It remains:

- bootstrap-safe;
- deterministic;
- independently implemented;
- callable from tests and diagnostics;
- selectable by a command-line/config mode;
- capable of reparsing a complete file or project.

The reference implementation may evolve with the language, but it must not be mechanically replaced by the same generated instruction stream used by the GPU backend. Independent implementation is valuable for differential verification.

### I-02 — One normative grammar per dialect

There are three primary dialects:

- `SimpleDialect`
- `ShellDialect`
- `SdnDialect`

Each has one versioned grammar manifest. Shared machinery does not imply shared syntax.

### I-03 — No silent fallback

Every operation that is not completed by its selected backend must produce a
`CpuWorkItem` or a fatal backend record. A log line is not sufficient.

### I-04 — GPU output is provisional until closure

A GPU result is publishable only when:

- all required CPU-global-name requests are patched;
- all recovery tasks are resolved or the parse is marked failed;
- no fatal invariant task remains;
- grammar and action hashes match;
- deterministic merge/commit succeeds.

### I-05 — Stable source coordinates

All internal spans use normalized UTF-8 byte offsets. An `OriginMap` converts
normalized offsets back to original byte/code-unit coordinates for diagnostics and
source-preserving tools.

### I-06 — Deterministic identity and ordering

Token IDs, region IDs, syntax-unit IDs, HIR IDs, CPU task IDs, patches, and diagnostics
must be stable for the same source snapshot and grammar version. Device scheduling order
must not affect the result.

### I-07 — Grammar changes are atomic

A grammar-changing pull request must update:

- the dialect manifest;
- the independent CPU reference implementation where needed;
- generated CPU/GPU tables;
- Tree-sitter projection and node mapping;
- positive and negative corpus cases;
- grammar-feature coverage metadata.

### I-08 — Small-input efficiency

GPU offload is selected by a cost model. One-line shell input, a small SDN file, or a
tiny source file should normally use scalar or SIMD CPU parsing unless already part of a
resident GPU batch.

### I-09 — Immutable snapshots

A parse operates on a versioned immutable `SourceSnapshot`. Incremental edits produce a
new snapshot and explicit mapping to the previous generation.

### I-10 — Recovery is CPU-owned

The GPU may detect and localize errors, emit expected-token sets, and preserve partial
output. It does not invent recovery edits in the first production design.

---

## 6. Target architecture

```text
                           +-------------------------+
                           |  Source/Input Service   |
                           | files, buffers, edits   |
                           +------------+------------+
                                        |
                                        v
                           +-------------------------+
                           | SourceSnapshot / Batch  |
                           | encoding + version + id |
                           +------------+------------+
                                        |
                 +----------------------+----------------------+
                 |                                             |
                 v                                             v
       +----------------------+                     +----------------------+
       | CpuReferenceParser   |                     | Placement / Cost     |
       | complete scalar path |                     | scalar/SIMD/GPU      |
       +----------+-----------+                     +----------+-----------+
                  |                                                |
                  | reference AST/HIR                               v
                  |                                    +----------------------+
                  |                                    | normalize -> UTF-8  |
                  |                                    | SIMD or GPU          |
                  |                                    +----------+-----------+
                  |                                                |
                  |                                                v
                  |                                    +----------------------+
                  |                                    | validate + classify  |
                  |                                    | ByteClassArena       |
                  |                                    +----------+-----------+
                  |                                                |
                  |                                                v
                  |                                    +----------------------+
                  |                                    | lexical-state scan   |
                  |                                    | OpaqueRegionArena    |
                  |                                    +----------+-----------+
                  |                                                |
                  |                                                v
                  |                                    +----------------------+
                  |                                    | delimiters + indent  |
                  |                                    | RegionArena          |
                  |                                    +----------+-----------+
                  |                                                |
                  |                                                v
                  |                                    +----------------------+
                  |                                    | tokenize + compact   |
                  |                                    | TokenArena           |
                  |                                    +----------+-----------+
                  |                                                |
                  |                                                v
                  |                                    +----------------------+
                  |                                    | SyntaxUnitMap        |
                  |                                    | fn/stmt/expr/blocks  |
                  |                                    +----------+-----------+
                  |                                                |
                  |                                                v
                  |                                    +----------------------+
                  |                                    | GPU local parsers    |
                  |                                    | ParsedHirArena       |
                  |                                    +----+------------+----+
                  |                                         |            |
                  |                          global requests |            | hard/fail
                  |                                         v            v
                  |                              +----------------+  +----------------+
                  |                              | CPU global     |  | CpuWorkTable   |
                  |                              | name service   |  | recovery/spill |
                  |                              +-------+--------+  +--------+-------+
                  |                                      |                    |
                  |                                      v                    v
                  |                              +----------------+  +----------------+
                  |                              | Name patches   |  | CPU reference  |
                  |                              | candidates/ids |  | recovery/tasks |
                  |                              +-------+--------+  +--------+-------+
                  |                                      |                    |
                  |                                      +---------+----------+
                  |                                                |
                  |                                                v
                  |                                    +----------------------+
                  |                                    | deterministic patch  |
                  |                                    | and merge            |
                  |                                    +----------+-----------+
                  |                                                |
                  |                                                v
                  |                                    +----------------------+
                  |                                    | GPU semantic/HIR/MIR |
                  |                                    | continuation         |
                  |                                    +----------+-----------+
                  |                                                |
                  +--------------------- compare/verify -----------+
                                                                   |
                                                                   v
                                                        compiler/interpreter/
                                                        editor/shell/SDN sink
```

---

## 7. Execution modes

### 7.1 Modes

| Mode | Normalization and structural work | Parsing/HIR | Global names | Recovery | Purpose |
|---|---|---|---|---|---|
| `cpu-reference` | scalar reference | complete CPU reference | CPU | CPU | Bootstrap, oracle, debugging, smallest dependency set |
| `cpu-simd` | SIMD fast path with scalar tails | complete CPU reference or table-driven CPU parser | CPU | CPU | Default high-performance CPU mode |
| `gpu-hybrid` | GPU for selected batches | GPU local parse and Parsed HIR | CPU authority | CPU on demand | Main production offload mode |
| `gpu-verify` | GPU plus sampled/full CPU replay | GPU result compared with reference | CPU | CPU | Development, CI, release qualification |
| `gpu-resident` | source/arenas retained on device | GPU local parse and semantic continuation | CPU compact request/patch only | CPU on demand | IDE workspace, large build, server/compiler daemon |
| `auto` | cost model chooses per batch/unit | chosen backend | CPU | CPU | User-facing default after stabilization |

### 7.2 Proposed options

```text
--frontend=cpu-reference
--frontend=cpu-simd
--frontend=gpu-hybrid
--frontend=gpu-verify
--frontend=gpu-resident
--frontend=auto

--frontend-verify=off|sample|file|full
--frontend-fallback=region|function|module|file
--frontend-audit=<path>
--gpu-strict
--gpu-resident-budget=<bytes>
--parser-dialect=simple|shell|sdn
--parser-entry=module|declaration|statement|expression|document|command
```

`--gpu-strict` is a development mode: any compatibility spill other than the two
mandatory CPU authorities fails the run. It is essential for measuring real GPU
coverage.

### 7.3 Placement policy

Placement is based on measured cost, not a fixed “GPU is always faster” rule.

Inputs to the cost model include:

- source bytes in the batch;
- source already resident on the GPU;
- number of files;
- expected token density;
- previous incremental arenas available;
- device transfer cost;
- kernel-launch cost;
- GPU occupancy and memory budget;
- recent spill rate for the dialect and grammar version;
- whether CPU global surfaces are cached;
- whether the request needs only an outline or a complete HIR.

The model must record the reason for its choice so performance regressions can be
diagnosed.

---

## 8. Shared data contracts

The same logical contracts are used by scalar, SIMD, and GPU backends. Physical storage
may differ, but serialization and comparison semantics are fixed.

### 8.1 `SourceSnapshot`

```simple
struct SourceSnapshot:
    snapshot_id: u64
    source_id: u64
    generation: u32
    path_id: u64

    original_encoding: EncodingId
    original_byte_count: u64
    normalized_utf8_byte_count: u64

    original_buffer: BufferRef
    utf8_buffer: BufferRef
    origin_map: OriginMapRef

    grammar_contract_hash: Hash256
    content_hash: Hash256
    previous_snapshot_id: u64?
```

Rules:

- `utf8_buffer` is immutable for the snapshot.
- A valid UTF-8 input may alias the original buffer.
- The snapshot records whether a BOM was consumed.
- Encoding is explicit through BOM, project configuration, API metadata, or a declared
  file rule. The compiler does not statistically guess an arbitrary legacy encoding.
- `OriginMap` maps normalized UTF-8 byte positions to original positions.

### 8.2 `OriginMap`

A full entry per code point is often too expensive. Use:

- one checkpoint per fixed-size normalized block;
- compact deltas for variable-width transformations;
- exact exception entries where a source code unit expands or contracts;
- a direct identity marker for ordinary UTF-8.

Required operations:

```text
normalized_byte -> original_byte/code_unit
original_byte/code_unit -> normalized_byte
normalized_span -> original span
```

Diagnostics must be able to report both normalized and original coordinates in debug
mode.

### 8.3 `ByteClassArena`

For each 64- or 128-byte block, store bit masks rather than one enum per byte where
possible:

```simple
struct ByteClassBlock:
    ascii: Mask
    utf8_lead2: Mask
    utf8_lead3: Mask
    utf8_lead4: Mask
    utf8_cont: Mask
    invalid: Mask

    whitespace: Mask
    newline: Mask
    digit: Mask
    ascii_ident_start: Mask
    ascii_ident_continue: Mask
    non_ascii_lead: Mask

    quote_double: Mask
    quote_single: Mask
    backslash: Mask
    hash: Mask
    slash: Mask

    lparen: Mask
    rparen: Mask
    lbracket: Mask
    rbracket: Mask
    lbrace: Mask
    rbrace: Mask

    colon: Mask
    comma: Mask
    dot: Mask
    semicolon: Mask
    operator_candidate: Mask
```

The dialect may add masks, but the common block format must remain versioned and
bounded.

### 8.4 `LexChunkSummary`

A chunk does not initially know whether it begins inside a string, comment, or raw
payload. It therefore emits an associative transition summary:

```simple
enum LexState:
    Normal
    DoubleString
    SingleString
    TripleString
    RawString
    LineComment
    RawBlock
    Invalid

struct LexChunkSummary:
    transition: [LexState; LEX_STATE_COUNT]
    first_error_offset: [u32; LEX_STATE_COUNT]
    end_escape_parity: [bool; LEX_STATE_COUNT]
    flags: u32
```

Composition is function composition:

```text
compose(a, b)(state) = b(a(state))
```

Because composition is associative, a device-wide prefix scan can calculate each
chunk’s true entry state.

The state set is dialect-defined. For example:

- Simple currently treats `#` as the normal line-comment introducer, while `//` is a
  language operator and must not be globally reclassified as a comment.
- Shell has distinct single-quote, double-quote, escape, substitution, and here-document
  states.
- SDN has its own string/comment rules.

### 8.5 `OpaqueRegionArena`

```simple
enum OpaqueKind:
    String
    RawString
    TripleString
    LineComment
    BlockComment
    RawPayload
    HereDocument
    Invalid

struct OpaqueRegion:
    region_id: u64
    kind: OpaqueKind
    start_byte: u64
    end_byte: u64
    parent_region_id: u64?
    flags: u32
```

Only grammar-manifest-supported region kinds are active. A future block-comment syntax
must not be inferred merely because a generic scanner supports it.

### 8.6 `TokenArena`

Use a structure-of-arrays representation:

```simple
struct TokenArena:
    kind: DeviceArray<TokenKindCode>
    start_byte: DeviceArray<u32_or_u64>
    end_byte: DeviceArray<u32_or_u64>
    line_id: DeviceArray<u32>
    flags: DeviceArray<u32>
    region_id: DeviceArray<u32>
    text_hash: DeviceArray<u64>
    aux: DeviceArray<u32>
```

Properties:

- token text normally remains a slice of the UTF-8 buffer;
- no per-token heap object is required;
- `end_byte` may be omitted for fixed/derivable cases, but the canonical comparison view
  exposes both start and end;
- text hashes are optional and can be lazy;
- line and column lookup uses a newline index, not repeated source scans;
- strings/raw blocks carry payload bounds and decode flags rather than eagerly copied
  strings.

### 8.7 `RegionArena`

```simple
enum RegionKind:
    Root
    Paren
    Bracket
    Brace
    Indent
    SpecialDelimiter
    String
    Comment
    RawBlock
    CustomBlock
    Invalid

struct RegionArena:
    kind: DeviceArray<RegionKind>
    start_token: DeviceArray<u32>
    end_token: DeviceArray<u32>
    parent: DeviceArray<u32>
    first_child: DeviceArray<u32>
    next_sibling: DeviceArray<u32>
    depth: DeviceArray<u16>
    flags: DeviceArray<u32>
```

This is the physical block map. It does not claim that a region is semantically an
`if`, function, or loop.

### 8.8 `SyntaxUnitMap`

The syntax-unit map is a cheap skeleton, not a completed parse.

```simple
enum SyntaxUnitKind:
    File
    Module
    Import
    Declaration
    TypeDeclaration
    TypeMember
    Function
    FunctionHeader
    FunctionBody
    Statement
    Expression
    Pattern
    TypeExpression
    Attribute
    ContractClause
    CustomBlock
    ShellCommand
    SdnValue
    Unknown

enum UnitState:
    Mapped
    Ready
    Parsing
    Parsed
    Deferred
    Failed

struct SyntaxUnit:
    unit_id: u64
    kind_hint: SyntaxUnitKind
    entry_rule_id: u32
    parent_unit_id: u64?
    start_token: u32
    end_token: u32
    start_byte: u64
    end_byte: u64
    region_id: u32
    dependency_begin: u32
    dependency_count: u32
    flags: u32
    state: UnitState
```

A function is mapped from a declaration keyword/header and its body region. Statements
are mapped from logical line boundaries and nested regions. Expressions are mapped from
statement grammar separators and delimiter regions.

If the skeleton cannot unambiguously select an entry rule, it emits a CPU work item
rather than pretending to have parsed the region.

### 8.9 `ParsedHirArena`

```simple
struct ParsedHirArena:
    kind: DeviceArray<HirKindCode>
    stable_id: DeviceArray<u64>
    parent_id: DeviceArray<u64>
    first_child: DeviceArray<u32>
    child_count: DeviceArray<u32>

    operand0: DeviceArray<u64>
    operand1: DeviceArray<u64>
    type_ref: DeviceArray<u64>
    symbol_ref: DeviceArray<u64>

    start_byte: DeviceArray<u64>
    end_byte: DeviceArray<u64>
    flags: DeviceArray<u32>
```

Important flags include:

```text
HIR_UNRESOLVED_LOCAL
HIR_UNRESOLVED_GLOBAL
HIR_HAS_GLOBAL_CANDIDATES
HIR_TYPE_PENDING
HIR_FROM_RECOVERY
HIR_PARTIAL
HIR_INVALID
```

### 8.10 `GlobalNameRequestArena`

```simple
struct GlobalNameRequest:
    request_id: u64
    snapshot_id: u64
    hir_id: u64
    module_id: u64
    lexical_scope_id: u64
    name_hash: u64
    name_start_byte: u64
    name_end_byte: u64
    namespace_mask: u32
    import_context_id: u64
    expected_category_mask: u32
    flags: u32
```

Only compact name/scope/interface data crosses to the CPU. The full HIR need not be
copied.

### 8.11 `PatchStream`

```simple
enum PatchKind:
    BindGlobalSymbol
    BindGlobalCandidateSet
    BindTypeSurface
    InsertRecoveryNode
    ReplaceTokenRange
    ReplaceHirRange
    AttachDiagnostic
    InvalidateUnit
    EscalateFallback
    MarkFatal

struct ParsePatch:
    patch_id: u64
    task_or_request_id: u64
    target_stable_id: u64
    kind: PatchKind
    payload_ref: u64
    deterministic_order_key: u128
    grammar_contract_hash: Hash256
```

Patches are sorted and checked before application. Two patches may not write the same
field unless the contract explicitly defines a merge operator.

---

## 9. GPU stage-by-stage design

### 9.1 Stage G0 — source batching and scheduling

Inputs are grouped by:

- dialect;
- grammar hash;
- encoding;
- requested entry rule;
- snapshot residency;
- output sink;
- verification mode.

The scheduler should batch many small source files rather than launch one kernel chain
per file. Per-file offset tables isolate boundaries.

Output:

```text
SourceBatchDescriptor[]
PlacementDecision[]
```

Failure tags:

```text
gpu.fail.device_unavailable
gpu.fail.unsupported_device
gpu.fail.memory_budget
gpu.fail.batch_descriptor
```

The first two normally select CPU/SIMD before work begins; they are placement records,
not parser errors.

### 9.2 Stage G1 — encoding selection

Encoding precedence:

1. API-provided encoding;
2. BOM;
3. project/file-rule declaration;
4. UTF-8 default.

Legacy encodings requiring large mapping tables use an explicit codec ID. Unsupported
codecs create:

```text
cpu.compat.encoding_codec:<codec-id>
```

Statistical encoding detection is not accepted for compiler source because an
incorrect guess changes program text.

### 9.3 Stage G2 — transcode to UTF-8

For UTF-16 and UTF-32, use a count/scan/emit scheme:

1. classify each code unit or surrogate pair;
2. compute the number of UTF-8 bytes;
3. exclusive-scan lengths to output offsets;
4. emit UTF-8;
5. emit compressed origin-map checkpoints;
6. record the earliest malformed input deterministically.

Latin-1 is a simpler one- or two-byte expansion.

Malformed encoding is not “repaired” silently. It creates either:

```text
cpu.required.error_recovery.encoding
```

for an editor/recovery request, or a fatal encoding diagnostic for strict compilation.

For small inputs, the CPU SIMD transcoder is normally cheaper.

### 9.4 Stage G3 — fused UTF-8 validation and byte classification

Read each UTF-8 byte block once and produce:

- UTF-8 lead/continuation validity;
- ASCII/non-ASCII masks;
- whitespace and newline masks;
- quote/backslash/comment candidates;
- delimiter candidates;
- operator/punctuation candidates;
- digit and identifier candidates.

This stage may tag delimiter **candidates**, but it cannot yet call them real block
boundaries because delimiters inside strings/comments/raw payloads are opaque.

The desired kernel output is a dense `ByteClassArena`, not a second copied character
array.

### 9.5 Stage G4 — lexical-state summaries

Each chunk executes the dialect lexical automaton for every possible entry state and
stores its transition summary. Prefix-scan composition yields the true entry state for
each chunk.

This handles cases such as a chunk beginning in the middle of:

- a quoted string;
- a raw/triple string;
- a line comment;
- a custom raw block;
- a shell quote or substitution;
- an SDN string.

The implementation should follow a general finite-state composition model rather than
a serial “thread 0 finds all prior quotes” pass.

Hard/fail tags:

```text
gpu.hard.lex_state:<state-id>
gpu.fail.lex_transition_invariant
gpu.fail.lex_state_overflow
impl.todo.lex_state:<state-id>
```

### 9.6 Stage G5 — opaque masks and text/comment region tags

Using true chunk entry states:

- calculate in-string/in-comment/in-raw masks;
- resolve escaped quotes;
- locate region starts and ends;
- emit `OpaqueRegionArena`;
- retain content as source slices.

All later structural masks use:

```text
actual_mask = candidate_mask & ~opaque_mask
```

### 9.7 Stage G6 — delimiter matching

The frontend handles generic structural pairs such as:

```text
( )
[ ]
{ }
```

and dialect-specific pairs such as Simple GPU launch delimiters when enabled by the
grammar.

One deterministic parallel strategy is:

1. compact all non-opaque delimiter events;
2. assign `+1` to opens and `-1` to closes;
3. prefix-scan total nesting depth;
4. pair an opener at `depth_before = d` with the corresponding closer at
   `depth_after = d`;
5. verify delimiter kind and ordering;
6. build parent/child links.

This generic-depth method exposes cross-kind mismatches such as `([)]`: the computed
pair at a depth has the wrong delimiter kind and becomes a recovery task.

Outputs:

- matching event index;
- region ID;
- parent region ID;
- depth;
- underflow/unclosed/mismatch records.

Failure tags:

```text
cpu.required.error_recovery.unclosed_delimiter
cpu.required.error_recovery.unexpected_closer
cpu.required.error_recovery.delimiter_mismatch
gpu.fail.delimiter_pair_invariant
```

### 9.8 Stage G7 — logical lines and indentation regions

The GPU already knows newlines, opaque regions, and delimiter depth. It can determine
logical lines by suppressing indentation significance for:

- blank lines;
- comment-only lines;
- continuation lines;
- lines inside bracketed/parenthesized expressions according to the dialect.

For each significant line:

1. find the first non-indent byte;
2. compute the configured indentation width;
3. compare with the structural indentation hierarchy;
4. build parent and next-sibling/end links using a parallel nearest-smaller or
   block-summary algorithm;
5. emit `INDENT`/`DEDENT` events and `Indent` regions.

Do not require a single GPU thread to maintain the whole file’s indentation stack.

Inconsistent dedent, forbidden tabs, or ambiguous mixed indentation emits:

```text
cpu.required.error_recovery.indent_inconsistent
cpu.required.error_recovery.indent_tab_policy
gpu.hard.indent_summary
gpu.fail.indent_parent_invariant
```

### 9.9 Stage G8 — token boundaries and token hints

The common path uses masks and neighboring classes to identify:

- identifiers and keywords;
- numeric literal candidates;
- string/raw payload tokens;
- punctuation;
- multi-character operators;
- indentation/newline;
- custom-block introducers.

Multi-character operators must handle chunk boundaries. Every chunk stores a small
prefix/suffix window or boundary summary.

For Unicode identifiers:

- ASCII is handled entirely by masks;
- only non-ASCII leading bytes are decoded;
- code points are checked against a versioned Simple identifier profile based on
  `XID_Start`/`XID_Continue`, plus any explicitly documented Simple additions or
  restrictions;
- the Unicode data version is part of the grammar contract hash.

Unknown Unicode tables or unsupported profiles emit:

```text
impl.todo.unicode_profile:<profile-version>
cpu.compat.unicode_identifier
```

### 9.10 Stage G9 — count, scan, and emit `TokenArena`

Avoid one atomic append per token.

1. each block counts tokens;
2. device scan assigns output ranges;
3. blocks emit into deterministic ranges;
4. a validation kernel checks non-overlap, monotonic offsets, and EOF.

String decoding, numeric conversion, and identifier hashing can be lazy. The token
preserves source bounds first.

### 9.11 Stage G10 — build the syntax-unit skeleton

This is mapping, not parsing.

The mapper uses:

- token kinds and keyword hints;
- delimiter/indent regions;
- logical-line boundaries;
- declaration introducers;
- grammar metadata describing safe unit boundaries.

Example:

```simple
fn add(a: i32, b: i32) -> i32:
    val sum = a + b
    return sum
```

can be mapped as:

```text
Unit Function          tokens 0..N
  Unit FunctionHeader  tokens 0..header_end
    Unit ParamList
  Unit FunctionBody
    Unit Statement     val ...
      Unit Expression  a + b
    Unit Statement     return ...
      Unit Expression  sum
```

The skeleton records entry rules but does not decide types, names, or operator overloads.

If a unit boundary cannot be proven, the mapper emits:

```text
gpu.hard.unit_boundary:<rule-id>
cpu.compat.reparse_region
impl.todo.unit_mapper:<feature-id>
```

### 9.12 Stage G11 — GPU local parser

#### 9.12.1 Parallelism model

Do not try to make every token in one tiny expression execute independently. Use two
levels:

- many functions/statements/expressions parse concurrently;
- a warp, subgroup, or workgroup executes the bounded local parser for one unit.

A sequential Pratt step inside one expression is acceptable when thousands of
expressions are processed in parallel.

#### 9.12.2 Grammar program

Accelerated parsers consume a generated, versioned grammar program:

```simple
enum GrammarOp:
    Match
    MatchSet
    MatchKeyword
    CallRule
    Return
    ChoiceByLookahead
    Optional
    Loop
    EnterNode
    ExitNode
    CaptureField
    EmitHir
    EmitSymbol
    EmitConstraint
    MarkUnit
    FailExpected
    DeferCpu

struct GrammarRule:
    rule_id: u32
    entry_pc: u32
    max_lookahead: u8
    output_kind: u16
    gpu_class: GpuSupportClass
    recovery_profile_id: u16
```

The GPU grammar is deterministic for normal Simple syntax. Ambiguous constructs must be
resolved by a documented bounded predicate or be explicitly classified as a CPU spill
until redesigned.

#### 9.12.3 Action program

Syntax recognition and output actions are separated:

```text
GrammarProgram -> accepted structure and captured fields
ActionProgram  -> AST/HIR/shell/SDN events
```

Action IDs are stable and hand-reviewed. The CPU reference parser remains independently
coded; accelerated CPU/GPU parsers share generated metadata and action IDs.

#### 9.12.4 Output sizing

Use either:

- a count pass followed by scan and emit; or
- a bounded per-unit scratch arena followed by compaction.

The count/scan/emit path is preferred for release determinism and memory accounting.

#### 9.12.5 Failure behavior

The GPU does not attempt synchronization recovery. On first local grammar failure it
records:

- entry rule;
- current token;
- expected set;
- parser stack summary;
- already emitted provisional range;
- smallest safe enclosing unit.

It then emits a `CpuWorkItem`.

### 9.13 Stage G12 — direct Parsed-HIR emission

Most Simple constructs can emit Parsed HIR directly:

| Source construct | Parsed-HIR result |
|---|---|
| variable declaration | declaration node, symbolic initializer |
| call | call node, symbolic callee, argument range |
| member access | member node with unresolved member symbol |
| arithmetic | generic operator HIR, type pending |
| function | function HIR with parameters, body, flags |
| trait/impl | declaration HIR with symbolic trait/type references |
| DI binding | DI metadata with symbolic endpoints |
| AOP advice | advice metadata and symbolic pointcut references |
| custom block | block HIR plus registered dialect payload/action |

A compatibility AST can be materialized by an adapter. The default production path
should avoid constructing and then walking a pointer-rich AST solely to create HIR.

### 9.14 Stage G13 — local symbols and local constraints

GPU local work includes:

- lexical scope construction;
- parameter/local declaration identity;
- local duplicate detection;
- local reference binding;
- capture-set generation;
- literal typing;
- generic operator/type constraints;
- local control-flow structure;
- effect/capability facts;
- local DI/AOP declarations;
- unresolved-global extraction.

A reference is global when it cannot be resolved in the local scope graph or when its
namespace explicitly requires a module/project lookup.

### 9.15 Stage C1 — CPU global-name authority

The CPU receives compact batches, not source reparses.

It owns:

- module and package identities;
- import/export graphs;
- visibility;
- global namespace partitioning;
- deterministic global symbol IDs;
- duplicate global declarations;
- global candidate-set discovery;
- cyclic import/name dependency reporting;
- cached module surfaces.

It returns:

```simple
struct GlobalNamePatch:
    request_id: u64
    hir_id: u64
    status: GlobalNameStatus
    bound_symbol_id: u64?
    candidate_set_ref: u64?
    surface_type_ref: u64?
    diagnostic_ref: u64?
```

Global-name resolution can be parallel CPU code and can use SIMD/hash acceleration.
It remains CPU authority even if the GPU assists sorting or hashing later.

### 9.16 Stage G14 — apply global patches and continue semantics

After patch validation, GPU work resumes:

- attach global symbol IDs/candidate sets;
- generate or complete type constraints;
- run type unification/fixpoints;
- select overloads and traits from CPU-supplied global candidate sets;
- perform capability/effect checks;
- instantiate generics;
- process DI allocation/layout metadata;
- process AOP matching/lowering;
- desugar;
- lower toward MIR or the existing next compiler contract.

If a non-name semantic algorithm is temporarily unavailable on GPU, it emits a
compatibility task. Such tasks are not permanent design exceptions.

### 9.17 Stage C2 — CPU recovery and diagnostic arbitration

Recovery uses the original CPU parser/recovery implementation through the shared
request contract.

The initial fallback granularity may be a whole module because the current parser is
module-oriented. As `ParserContext` and entry-rule support mature, fallback narrows:

```text
region -> statement -> function -> module -> file
```

CPU recovery returns:

- repaired/partial CST or HIR nodes;
- skipped/inserted token records;
- stable diagnostics;
- a resume boundary or an escalation request.

### 9.18 Stage G15/C3 — deterministic merge and commit

The merge controller:

1. sorts work and patches by deterministic order;
2. validates snapshot and grammar hashes;
3. rejects conflicting patches;
4. applies name patches;
5. applies recovery patches;
6. invalidates dependent units;
7. reruns only affected GPU stages;
8. publishes the final result.

A GPU kernel failure cannot leave partially published HIR.

---

## 10. CPU work table

The CPU work table is the central coordination structure for hard cases, failures,
compatibility gaps, and required CPU authority.

### 10.1 Support classes

```simple
enum BackendSupportClass:
    G0GpuNative
    G1GpuNativeVerify
    G2GpuSpillSupported
    C0CpuRequired
    X0NeedsImplementation
    F0FatalInvariant
```

Meanings:

- `G0GpuNative`: completed on GPU in production.
- `G1GpuNativeVerify`: completed on GPU; sampled CPU verification requested.
- `G2GpuSpillSupported`: CPU implementation exists; GPU coverage is incomplete.
- `C0CpuRequired`: deliberate CPU authority, currently global names or recovery.
- `X0NeedsImplementation`: no correct handler is available for this feature/path.
- `F0FatalInvariant`: internal corruption or impossible state; do not continue.

### 10.2 Task kinds

```simple
enum CpuTaskKind:
    GlobalNameResolution
    ErrorRecovery
    EncodingFallback
    Utf8RepairOrDiagnostic
    ReparseRegion
    ReparseStatement
    ReparseFunction
    ReparseModule
    ReparseFile
    VerifyRegion
    UnsupportedGrammarRule
    UnsupportedSemanticAction
    CustomBlockCpu
    ResourceSpill
    DeviceFailure
    GrammarDivergence
    NeedsImplementation
    FatalInvariant
```

### 10.3 Task status

```simple
enum CpuWorkStatus:
    Detected
    Queued
    Claimed
    Running
    Resolved
    Patched
    Escalated
    NeedsImplementation
    Fatal
    Merged
```

### 10.4 Row schema

```simple
struct CpuWorkItem:
    task_id: u64
    snapshot_id: u64
    source_id: u64
    generation: u32

    dialect_id: u32
    grammar_contract_hash: Hash256
    stage_id: u16
    entry_rule_id: u32

    support_class: BackendSupportClass
    task_kind: CpuTaskKind
    status: CpuWorkStatus
    reason_code: u32

    region_id: u64?
    syntax_unit_id: u64?
    hir_id: u64?

    start_byte: u64
    end_byte: u64
    start_token: u32
    end_token: u32

    parser_state_ref: u64?
    expected_set_ref: u64?
    partial_output_ref: u64?
    dependency_set_ref: u64?

    attempted_backend: BackendId
    fallback_scope: FallbackScope
    attempt_count: u16

    deterministic_order_key: u128
    sample_hash: Hash256

    first_seen_revision: RevisionId
    last_seen_revision: RevisionId
    occurrence_count: u64

    owner_tag: TagId?
    issue_tag: TagId?
```

### 10.5 Stable reason tags

Human-readable tags are generated from stable numeric reason codes.

#### Mandatory CPU tags

```text
cpu.required.global_name
cpu.required.global_name.module_graph
cpu.required.global_name.import_visibility
cpu.required.global_name.duplicate
cpu.required.error_recovery
cpu.required.error_recovery.encoding
cpu.required.error_recovery.delimiter
cpu.required.error_recovery.indent
cpu.required.error_recovery.grammar
```

#### GPU-hard compatibility tags

```text
gpu.hard.lex_state:<state-id>
gpu.hard.indent:<profile-id>
gpu.hard.unit_boundary:<rule-id>
gpu.hard.rule:<rule-id>
gpu.hard.action:<action-id>
gpu.hard.custom_block:<block-id>
gpu.hard.semantic:<pass-id>
```

#### GPU/backend failure tags

```text
gpu.fail.device
gpu.fail.launch
gpu.fail.memory_budget
gpu.fail.queue_overflow
gpu.fail.arena_overflow
gpu.fail.timeout
gpu.fail.verify
gpu.fail.internal_invariant
```

#### Work-to-implement tags

```text
impl.todo.rule:<rule-id>
impl.todo.action:<action-id>
impl.todo.lex_state:<state-id>
impl.todo.unicode_profile:<version>
impl.todo.custom_block:<block-id>
impl.todo.semantic:<pass-id>
```

#### Grammar-divergence tags

```text
grammar.divergence.compiler_reference:<feature-id>
grammar.divergence.accelerated:<feature-id>
grammar.divergence.outline:<feature-id>
grammar.divergence.tree_sitter:<feature-id>
grammar.divergence.interpreter:<feature-id>
grammar.divergence.shell:<feature-id>
grammar.divergence.sdn_simple:<feature-id>
grammar.divergence.sdn_rust:<feature-id>
```

#### Fallback-scope tags

```text
fallback.scope:region
fallback.scope:statement
fallback.scope:function
fallback.scope:module
fallback.scope:file
```

### 10.6 GPU emission without nondeterministic atomics

Task creation uses count/scan/emit:

1. units mark zero or more task flags;
2. a scan assigns task slots;
3. task rows are emitted to deterministic positions;
4. CPU sorts by `deterministic_order_key`.

A bounded emergency queue is permitted only for fatal device events and must itself be
audited.

### 10.7 CPU scheduler

```text
read queued tasks
  -> validate snapshot/grammar hashes
  -> stable sort by:
       mandatory authority before compatibility
       source_id
       byte range
       task kind
       task id
  -> group by (task_kind, dialect, entry_rule)
  -> execute CPU handlers
  -> emit patches or escalation
  -> repeat until fixed point or fatal
```

Global-name tasks are additionally grouped by project/module graph.

### 10.8 Escalation

A failed local CPU task escalates predictably:

```text
region -> statement -> function -> module -> file
```

Each escalation creates a new task row linked to the previous row. It does not mutate
history into invisibility.

### 10.9 Persistent audit output

Every accelerated parse can emit:

```text
build/audit/frontend_work.sdn
```

Suggested summary:

```sdn
run:
  grammar_hash: ...
  backend: gpu-hybrid
  sources: 1234
  bytes: 987654321

counts:
  cpu_required_global_name: 18220
  cpu_required_recovery: 0
  gpu_compat_spills: 7
  needs_implementation: 1
  fatal: 0

work:
  - task_id: ...
    tag: impl.todo.rule:pattern_guard
    path: ...
    span: ...
    sample_hash: ...
    first_seen: ...
    occurrence_count: ...
```

A repository baseline can live at:

```text
config/check/frontend_work_baseline.sdn
```

Policy:

- mandatory global-name requests are measured but not treated as regressions;
- valid-corpus recovery tasks are failures;
- new `impl.todo.*` rows fail the push gate;
- new compatibility-spill reason codes fail unless explicitly baselined;
- known compatibility rows may only stay equal or decrease;
- fatal rows always fail;
- sample hashes retain minimized reproducible examples.

### 10.10 Developer query interface

```text
simple frontend-work list --status needs-implementation
simple frontend-work list --tag 'gpu.hard.rule:*'
simple frontend-work show <task-id>
simple frontend-work repro <task-id>
simple frontend-work group --by rule
simple frontend-work group --by source
simple frontend-work diff <old-audit> <new-audit>
simple frontend-work emit-issue <task-id>
```

This is how CPU-side developers and LLM agents find exact GPU TODO work without reading
unstructured logs.

---

## 11. Mapping graph and traceability

Every representation change emits relations into a compact mapping graph.

### 11.1 Required edges

```text
OriginalSpan       -> NormalizedSpan
NormalizedByte     -> ByteClassBlock
OpaqueRegion       -> SourceSpan
Token              -> SourceSpan
Token              -> Region
Region             -> ParentRegion
SyntaxUnit         -> TokenRange
SyntaxUnit         -> Region
HirNode            -> SyntaxUnit
HirNode            -> SourceSpan
GlobalNameRequest  -> HirNode
CpuWorkItem        -> SyntaxUnit/HirNode/SourceSpan
ParsePatch         -> CpuWorkItem/GlobalNameRequest
Diagnostic         -> SourceSpan/CpuWorkItem/HirNode
OldSnapshotUnit    -> NewSnapshotUnit
```

### 11.2 Why this matters

The map allows:

- CPU work to select the smallest safe source range;
- diagnostics to return to original encoding coordinates;
- incremental invalidation;
- CPU/GPU differential comparison;
- Tree-sitter node correlation;
- work-table reproduction;
- profiling by language feature;
- proof that a fallback was explicit.

### 11.3 Stable IDs

A practical stable ID can combine:

```text
source_id
snapshot generation
grammar feature/rule id
normalized start/end
local ordinal
```

For incremental identity reuse, unchanged units inherit IDs through the old-to-new
mapping. Content-only hashes are insufficient when identical statements occur multiple
times.

---

## 12. CPU global-name service design

### 12.1 Inputs

The GPU emits:

- module surface declarations;
- imports/exports;
- visibility;
- namespace categories;
- unresolved global names;
- local expected-category/type hints;
- dependency edges.

### 12.2 CPU-owned operations

The CPU service performs:

1. deterministic project/module ordering;
2. module/package identity;
3. import/export expansion;
4. visibility checks;
5. duplicate global declaration detection;
6. global name lookup;
7. candidate-set creation;
8. cycle diagnostics;
9. stable symbol-ID assignment;
10. surface-cache update.

### 12.3 Outputs

The CPU does not lower expressions. It emits compact patches:

```text
bound symbol
candidate set
declared surface type
visibility result
unresolved/ambiguous diagnostic
```

### 12.4 Caching

Cache key:

```text
module source hash
grammar hash
public surface hash
import graph generation
configuration/variation tags
```

A private body edit that does not alter a module surface should not invalidate unrelated
global-name results.

### 12.5 Avoiding a CPU bottleneck

- Transfer only surface and request tables.
- Sort/hash requests on GPU before transfer if profitable.
- Resolve CPU batches in parallel, but commit symbol IDs deterministically.
- Cache module surfaces.
- Apply one patch batch per project wave, not one callback per name.
- Measure global-name bytes and latency separately from GPU parser time.

---

## 13. CPU error-recovery service design

### 13.1 Valid-source fast path

No recovery CPU work occurs for valid input. Error detection can remain on GPU; recovery
policy remains CPU-owned.

### 13.2 Recovery request

```simple
struct RecoveryRequest:
    task_id: u64
    snapshot_id: u64
    dialect_id: u32
    entry_rule_id: u32
    safe_unit_id: u64
    start_token: u32
    end_token: u32
    failure_token: u32
    expected_set_ref: u64
    parser_stack_summary_ref: u64
    provisional_hir_ref: u64?
    mode: RecoveryMode
```

### 13.3 Modes

| Mode | Behavior |
|---|---|
| strict compile | produce stable diagnostics; fail the affected compilation unit |
| multi-error compile | synchronize and continue to collect bounded errors |
| IDE/outline | produce partial nodes and error nodes |
| interactive interpreter | recover to statement boundary where safe |
| shell | recover to command/list/control-flow boundary |
| SDN | recover to collection/member/document boundary where policy permits |

### 13.4 Existing recovery reuse

The current compiler recovery code already contains:

- common mistakes from other languages;
- “did you mean” suggestions;
- skip-to-newline/token/brace;
- token insertion;
- context popping;
- bounded multi-error collection.

Wrap this implementation first. Do not rewrite recovery while introducing GPU parsing.

### 13.5 Diagnostic determinism

Diagnostics are sorted by:

```text
original source position
severity
stable diagnostic code
recovery task order
```

When GPU and CPU detect the same root error, the CPU recovery diagnostic wins and the
GPU detection remains attached as trace metadata.

### 13.6 Partial output

Recovered output is explicitly marked:

```text
HIR_FROM_RECOVERY
HIR_PARTIAL
```

Strict code generation rejects these flags. IDE and analysis clients may consume them.

---

## 14. SIMD optimization plan

### 14.1 Objective

`cpu-simd` must provide a low-latency path for:

- small and medium source files;
- systems without a suitable GPU;
- bootstrap-adjacent host tools;
- shell input;
- small SDN documents;
- differential verification of GPU masks.

It uses the same normalized buffers, masks, tokens, regions, and work-table contracts as
the GPU path.

### 14.2 Build on existing runtime dispatch

Extend the current runtime SIMD infrastructure with a parser-classification API:

```c
rt_parse_classify_utf8(...)
rt_parse_lex_summaries(...)
rt_parse_token_candidates(...)
rt_parse_compact_offsets(...)
```

Backends:

```text
scalar
SSE2/SSSE3
AVX2
AVX-512
NEON
SVE
RISC-V Vector
WASM SIMD
```

Not every backend is required in the first phase. Scalar, AVX2, and AArch64 NEON form a
practical initial set because the repository already has adjacent support.

### 14.3 Fused vector pass

For each 64/128-byte group:

- validate UTF-8;
- test all-ASCII;
- classify whitespace/newlines;
- classify ASCII identifier/digit bytes;
- classify quotes/backslashes/comment candidates;
- classify delimiters and punctuation;
- output masks.

Avoid:

```text
validate bytes
then scan bytes for quotes
then scan bytes for newlines
then scan bytes for tokens
```

The masks can be reused by all later stages.

### 14.4 ASCII and non-ASCII paths

- Pure ASCII blocks take the fastest mask path.
- Non-ASCII blocks run full vector UTF-8 validation where available.
- Non-ASCII lead positions are compacted for Unicode identifier-property lookup.
- Scalar tails and difficult boundary sequences use the same reference validators.

The current AVX2 “ASCII skip plus scalar non-ASCII” implementation is a correct bridge,
but should be benchmarked against a complete vector algorithm or a `simdutf` backend.

### 14.5 Quote and escape masks

Use branchless block algorithms:

1. identify backslashes;
2. compute odd-length escape runs;
3. remove escaped quote bits;
4. prefix-XOR unescaped quote bits to form in-string masks;
5. carry quote/escape state across blocks.

Dialect state composition extends this to raw/triple strings and shell quoting.

### 14.6 Line comments

For Simple’s ordinary `#` line comments:

- keep `#` candidates outside strings/raw regions;
- map each candidate to the next newline;
- union comment ranges;
- mask their delimiters and token candidates.

Do not reinterpret `//` as a generic comment. It is currently a Simple operator.

### 14.7 Token compaction

- use `popcount` to count token starts in a mask;
- prefix-scan block counts;
- emit offsets/kinds into fixed output ranges;
- retain source slices;
- parse numbers/strings lazily or in vector batches.

### 14.8 CPU parallelism

SIMD and multicore are separate dimensions. Large CPU-only batches should:

- assign independent files or syntax units to worker threads;
- use SIMD inside each worker;
- preserve deterministic output slots from a precomputed scan;
- avoid a global token append lock.

### 14.9 Transcoding

Evaluate two implementations:

1. extend Simple’s native runtime SIMD code;
2. use or adapt `simdutf` for validated conversion among UTF-8, UTF-16, UTF-32, and
   Latin-1.

The parser still needs Simple-specific structural masks even if transcoding delegates to
`simdutf`.

### 14.10 SIMD validation matrix

Every backend must be tested at every vector boundary for:

- 2/3/4-byte UTF-8 sequences split at each byte;
- overlong encodings;
- surrogates;
- values beyond `U+10FFFF`;
- truncated input;
- escaped quote runs;
- strings/comments crossing blocks;
- CRLF and LF;
- delimiter sequences crossing blocks;
- non-ASCII identifiers;
- UTF-16 surrogate pairs crossing chunks;
- origin-map conversion.

### 14.11 Performance measurements

Measure:

- GB/s for normalization/classification, but do not turn external benchmark numbers into
  Simple targets without local evidence;
- cycles/byte;
- tokens/s;
- time to first token and first HIR;
- allocations;
- peak memory;
- branch misses;
- scalar/SIMD crossover;
- SIMD/GPU crossover.

---

## 15. Shared parser runtime

### 15.1 Unify runtime, not language

```text
ParseRuntime
  SourceSnapshot
  OriginMap
  ByteClassArena
  LexStateEngine
  OpaqueRegionArena
  TokenArena
  RegionArena
  SyntaxUnitMap
  GrammarProgram VM
  ActionProgram
  CpuWorkTable
  MappingGraph
  DiagnosticArena
  IncrementalCache

Dialects
  SimpleDialect
  ShellDialect
  SdnDialect
```

### 15.2 `ParseDialect`

```simple
struct ParseDialect:
    dialect_id: u32
    dialect_version: Version
    grammar_contract_hash: Hash256

    lex_profile: LexProfileRef
    delimiter_profile: DelimiterProfileRef
    indentation_profile: IndentationProfileRef
    unicode_profile: UnicodeProfileRef

    grammar_program: GrammarProgramRef
    action_program: ActionProgramRef
    recovery_profile: RecoveryProfileRef
    tree_sitter_projection: TreeSitterProjectionRef

    entry_rules: EntryRuleTableRef
    feature_table: GrammarFeatureTableRef
```

### 15.3 `ParseRequest`

```simple
struct ParseRequest:
    snapshot: SourceSnapshotRef
    dialect: ParseDialectRef
    entry_rule: EntryRuleId

    backend_mode: ParseBackendMode
    output_mode: ParseOutputMode
    recovery_mode: RecoveryMode
    verify_mode: VerifyMode

    previous_result: ParseResultRef?
    edit_set: EditSetRef?
    memory_budget: u64
```

### 15.4 `ParseResult`

```simple
struct ParseResult:
    snapshot_id: u64
    grammar_contract_hash: Hash256

    token_arena: TokenArenaRef?
    region_arena: RegionArenaRef?
    syntax_units: SyntaxUnitMapRef?
    cst: CstRef?
    ast: AstRef?
    parsed_hir: ParsedHirArenaRef?
    final_hir: HirRef?

    cpu_work: CpuWorkTableRef
    diagnostics: DiagnosticArenaRef
    mapping_graph: MappingGraphRef

    completeness: ParseCompleteness
    backend_receipt: BackendReceipt
```

### 15.5 Output sinks

The parser runtime emits events to a sink:

```simple
trait ParseActionSink:
    fn begin_node(kind, span, stable_id)
    fn field(field_id, value_ref)
    fn token(token_id)
    fn emit_symbol(symbol_event)
    fn emit_constraint(constraint_event)
    fn end_node(stable_id)
```

Implementations:

- `SimpleParsedHirSink`
- `SimpleAstCompatibilitySink`
- `OutlineSink`
- `InterpreterSink` or `InterpreterAstAdapter`
- `ShellAstSink`
- `SdnValueSink`
- `TreeSitterProjectionSink` for generated metadata/tests, not runtime replacement of the
  native parser.

### 15.6 Parser backends

```text
CpuReferenceBackend    independently coded current parser
CpuTableBackend        generated grammar VM, scalar
CpuSimdBackend         SIMD frontend + CpuTableBackend or reference parser
GpuHybridBackend       GPU frontend/parser + CPU authority services
GpuResidentBackend     resident arenas and incremental state
TreeSitterBackend      editor CST projection
```

All backends return `ParseResult`.

---

## 16. Canonical grammar manifests

### 16.1 Files

```text
spec/grammar/grammar_schema.sdn
spec/grammar/simple.sdn
spec/grammar/shell.sdn
spec/grammar/sdn.sdn
spec/grammar/unicode_profile.sdn
```

### 16.2 Manifest content

A grammar manifest records:

```text
tokens
keywords
lexical states
comment and string forms
delimiter pairs
indentation policy
operator precedence and associativity
productions
bounded lookahead predicates
entry rules
semantic action IDs
recovery synchronization sets
GPU support classes
Tree-sitter node/projection metadata
feature IDs
language-version gates
```

Example sketch:

```sdn
feature:
  id: simple.fn_decl
  since: 1.0
  entry_rule: declaration
  gpu: native
  tree_sitter: exact

production:
  id: fn_decl
  rule:
    seq:
      - modifiers?
      - KW_FN
      - IDENT
      - generic_params?
      - param_list
      - return_type?
      - contract?
      - COLON
      - block
  action: emit_fn_hir
  recovery_sync: [NEWLINE, DEDENT, EOF]
```

### 16.3 Bootstrap-cycle avoidance

The compiler must not need the full mutable SDN implementation to parse its own grammar
manifest during the earliest bootstrap stage.

Use:

- checked-in generated tables;
- a frozen small bootstrap reader (`Sdn0`) or the Rust bootstrap SDN parser for the
  generator;
- generator version and input hash embedded in every artifact;
- a gate that regenerates and compares artifacts.

Normal compiler execution consumes generated tables, not live grammar SDN.

### 16.4 Generated artifacts

```text
src/generated/parse/simple_tokens.*
src/generated/parse/simple_cpu_tables.*
src/generated/parse/simple_gpu_program.*
src/generated/parse/simple_actions.*
src/generated/parse/simple_feature_map.sdn

src/generated/parse/shell_*
src/generated/parse/sdn_*

src/generated/tree_sitter_simple/grammar.js
src/generated/tree_sitter_simple/src/parser.c
src/generated/tree_sitter_simple/src/node-types.json
src/generated/tree_sitter_simple/src/scanner.c

spec/compiler_schema/registry/compiler.frontend.Grammar.sdn
```

The exact repository paths may be adjusted to existing generation policy, but ownership
must remain clear.

### 16.5 Independent CPU reference

The manifest is normative. The CPU reference is an independent executable oracle.
A grammar-change pull request changes both where necessary. A parity suite proves that
the independent implementation and generated accelerated implementations accept and
reject the same corpus and produce canonically equivalent output.

### 16.6 Grammar support metadata

Every production and action has a row:

| Feature/rule | CPU reference | CPU table | SIMD | GPU | Tree-sitter | Interpreter | Shell/SDN projection |
|---|---:|---:|---:|---:|---:|---:|---:|
| `simple.fn_decl` | exact | exact | exact | native | exact | exact | n/a |
| `simple.custom.sql_block` | exact | exact | exact | spill/native | external scanner/projected | exact | n/a |
| ... | ... | ... | ... | ... | ... | ... | ... |

No blank cell is allowed. Unsupported cells carry a stable reason tag.

---

## 17. Consumer-specific unification plan

### 17.1 Simple compiler

#### Current role

The current core parser is the complete executable reference and produces a flat/indexed
AST that is bridged to richer frontend structures.

#### Target

```text
ParserService(SimpleDialect)
  -> CpuReferenceBackend
  -> CpuSimdBackend
  -> GpuHybridBackend
  -> GpuResidentBackend
```

#### Migration

1. Wrap current `core/parser.spl` and lexer as `CpuReferenceBackend` without semantic
   changes.
2. Add canonical token/AST/HIR comparison serializers.
3. Introduce `ParserContext` behind the adapter.
4. Make every existing entry point call `ParserService`.
5. Preserve `flat_ast_bridge` for reference-parser output.
6. Add `ParsedHirAdapter` for GPU/table-parser output.
7. Move HIR lowering consumers gradually from rich AST objects to stable Parsed-HIR
   contracts.
8. Keep AST materialization selectable for tools and debugging.
9. Include grammar hash in parser and module-cache keys.

#### Required refactor

The module-global parser/lexer state must become context-owned before safe parallel
multi-file parsing. This is a correctness refactor, not merely a GPU optimization.

```simple
struct ParserContext:
    snapshot: SourceSnapshotRef
    token_cursor: u32
    parser_stack: ParserStack
    scope_stack: ScopeStack
    diagnostics: DiagnosticArenaRef
    scratch: ArenaRef
    options: ParseOptions
```

Do not move all globals in one commit. Migrate one state family at a time, with full
bootstrap and corpus parity after each move.

### 17.2 Simple interpreter

#### Target

The interpreter calls:

```text
ParserService.parse(
  dialect = SimpleDialect,
  entry = Module | Statement | Expression,
  backend = auto
)
```

For ordinary REPL input, `auto` normally selects CPU reference or CPU SIMD. A resident
IDE/interpreter workspace may reuse GPU arenas.

#### Output choices

Preferred:

```text
Parsed HIR -> interpreter evaluator
```

Compatibility:

```text
Parsed HIR -> InterpreterAstAdapter -> existing evaluator
```

#### Migration

1. Verify the actual resolution and callers of `lib.parser.parser`.
2. Build a feature corpus comparing compiler and interpreter acceptance.
3. Add module/statement/expression entry rules to `ParserService`.
4. Route interpreter parsing through the service in shadow mode.
5. Compare AST/evaluation results.
6. switch default;
7. retain the old parser as a temporary compatibility backend;
8. delete only after zero-call and parity gates.

### 17.3 Tree-sitter and editor parsing

#### Rename the current component

Rename current handwritten `TreeSitter`/outline types to avoid ambiguity:

```text
TreeSitter              -> LegacyOutlineParser or SimpleOutlineParser
parse_with_treesitter   -> parse_outline_legacy
```

Compatibility aliases may remain temporarily.

#### Add a real native grammar

Generate or check `tree-sitter-simple` from the canonical Simple grammar manifest.

Use an external scanner for constructs not expressible as ordinary regex tokens, such
as:

- indentation;
- raw/custom block boundaries;
- any context-sensitive string delimiter that Tree-sitter requires help to identify.

#### Role separation

- compiler CPU reference: executable language oracle;
- canonical manifest: normative grammar source;
- native Tree-sitter: incremental, error-tolerant editor CST;
- GPU `RegionArena`/`SyntaxUnitMap`: compiler structural index.

Tree-sitter must not become the compiler’s sole parser.

#### Incremental flow

```text
old tree
  -> apply edit ranges
  -> parse with old tree
  -> changed_ranges
  -> map changed ranges to syntax units
  -> invalidate compiler/GPU units
```

#### Outline

The outline becomes:

```text
Tree-sitter CST or SyntaxUnitMap
  -> OutlineSink
```

It no longer re-parses declarations with an independent grammar.

#### Query checks

Generated or handwritten queries for highlighting, symbols, injections, and locals must
be validated against generated `node-types.json`. A query referencing a removed node
fails the gate.

### 17.4 SimpleOS shell

#### Separate dialect, shared runtime

Shell syntax is not Simple syntax. It gets `ShellDialect` but reuses:

- source snapshots;
- UTF-8 validation;
- lexical-state engine;
- token/region arenas;
- grammar VM;
- CPU work table;
- diagnostics;
- incremental mapping.

#### One shell AST

```simple
enum ShellWordPart:
    Literal
    SingleQuoted
    DoubleQuoted
    Escape
    VariableExpansion
    CommandSubstitution
    Glob
    BraceExpansion

struct ShellCommand:
    words: [ShellWord]
    redirects: [ShellRedirect]
    assignments: [ShellAssignment]

enum ShellNode:
    Command
    Pipeline
    AndOrList
    Background
    If
    While
    For
    Case
    Function
    Sequence
```

Parsing and expansion must remain separate. Quote mode is preserved in `ShellWordPart`;
the parser does not flatten everything to text and then try to recover quoting.

#### Migration order

1. Introduce a shared shell lexer and golden token corpus.
2. Replace `_split_simple` and `parse_pipeline` quote scanning with the shared token
   stream.
3. Make redirects consume the same tokens.
4. Port control-flow parsing from line-text tests to `ShellDialect`.
5. Move expansion after AST creation.
6. retain old functions as compatibility wrappers;
7. compare command execution results;
8. remove duplicate scanners after parity.

#### GPU policy

Interactive shell lines default to scalar/SIMD. GPU parsing is useful for:

- large `.shs` scripts;
- batches of scripts;
- scripts already in a resident development workspace.

Command lookup/PATH resolution is runtime behavior, not parser global-name resolution.

#### Embedded Simple

A shell node that contains an explicitly embedded Simple expression/block invokes
`SimpleDialect` with a bounded entry rule. It does not copy Simple expression grammar
into `ShellDialect`.

### 17.5 SDN

#### One dialect contract

`SdnDialect` defines:

- scalars;
- quoted strings and escapes;
- inline arrays/dicts;
- indentation mappings/sequences;
- `:` and any supported `=` forms;
- table syntax;
- comments;
- duplicate-key policy;
- spans/issues;
- strict/untrusted limits.

#### Bootstrap authority

Keep the Rust SDN parser as the bootstrap oracle until:

- the manifest is complete;
- the Simple shared-runtime implementation passes the golden corpus;
- generated Rust and Simple tables agree;
- schema/config bootstraps pass from scratch.

#### Event sink

The target is genuinely one pass through parser actions:

```text
Sdn parse events
  -> ValueBuilder
  -> SpanBuilder
  -> IssueBuilder
  -> optional schema validator
```

`parse_with_spans_and_issues` should not parse or structurally rescan the document
multiple times.

#### Migration

1. Extract a feature matrix from both implementations.
2. Run every repository `.sdn` file through both and record differences.
3. Decide each difference in the manifest; do not choose by accident.
4. Generate Rust and Simple token/grammar metadata.
5. Port Simple parser to the shared runtime.
6. Add handler/event parity.
7. retain Rust parser for bootstrap and independent verification.
8. add GPU batch parsing for large SDN workloads only after CPU parity.

---

## 18. Grammar-divergence audit and fixes

| ID | Divergence surface | Risk | Evidence at baseline | Required action |
|---|---|---:|---|---|
| GD-01 | core parser vs `parser_factory` lifecycle/types | high | separate parser state/ownership abstractions | expose only `ParserService`; adapters hide legacy lifecycle |
| GD-02 | core parser vs handwritten outline parser | critical | outline parser independently dispatches most declarations | stop adding grammar there; generate/project outline |
| GD-03 | core parser vs heuristic partial parser | high | line/indent prefix recognition is independent | make partial tree a CPU recovery/outline sink |
| GD-04 | compiler parser vs interpreter parser | critical | interpreter imports separate parser surface; earlier unification report predates current frontend | shadow-parse and migrate interpreter entry rules |
| GD-05 | shell control parser vs pipeline quote scanner | critical | separate quote and escape logic | shared `ShellDialect` token stream |
| GD-06 | shell pipeline splitter vs word splitter vs redirects | critical | repeated splitting/interpretation | one lossless Shell AST |
| GD-07 | Simple SDN vs Rust SDN lexer | critical | token sets, spans, indentation differ | canonical `SdnDialect`, generated metadata, golden corpus |
| GD-08 | Simple SDN parser vs its own lexer | high | main parser performs direct text/line scans | route through shared token/region runtime |
| GD-09 | grammar registry vs actual language authority | high | registry is generated from selected implementation source | generate registry from canonical manifest |
| GD-10 | “TreeSitter” naming vs native implementation | medium/high | no native grammar artifact found in baseline search | rename legacy outline parser; add real grammar |
| GD-11 | frontend comments/documented pipeline vs active path | medium | orchestration comments and actual bridge/cache paths need verification | add architecture contract tests and update comments |
| GD-12 | lexer byte/code-point coordinate bases | critical | existing bug history and compatibility code | normalized UTF-8 byte spans + `OriginMap` |
| GD-13 | duplicate token-kind definitions/wire codes | high | existing lexer comments describe ordinal/wire-code mismatch risk | one generated stable token-code registry |
| GD-14 | custom/domain blocks across parsers | high | block start/payload/end and outline handling can diverge | manifest-owned block registry and action IDs |

### 18.1 Immediate divergence gate

Generate:

```text
build/audit/grammar_surfaces.sdn
```

Each feature row contains:

```text
feature_id
manifest version
CPU reference support
accelerated CPU support
GPU support class
Tree-sitter node mapping
interpreter support
outline support
shell/SDN relevance
positive corpus count
negative corpus count
```

Add:

```text
scripts/check/check-parser-surface-parity.shs
```

Push fails when:

- a parser surface appears without inventory;
- a feature row disappears unexpectedly;
- a token code changes without versioning;
- generated artifacts are stale;
- a Tree-sitter node/query is stale;
- a new `impl.todo.*` reason appears.

---

## 19. Repository layering and refactor target

The common parser runtime must not live only inside the compiler, because shell and SDN
must use it without importing the compiler driver.

### 19.1 Proposed dependency layers

```text
Layer 0: parse contracts
  source snapshot, spans, token/region/HIR IDs, work table schemas
  no GPU, compiler, shell, or SDN dependency

Layer 1: parse runtime
  arenas, grammar VM, action sink, mapping graph, diagnostics
  depends only on Layer 0 and core collections/memory

Layer 2: execution backends
  scalar, SIMD, GPU primitives
  depend on Layers 0-1 and platform/compute abstractions

Layer 3: dialects
  SimpleDialect, ShellDialect, SdnDialect
  depend on Layers 0-2 and generated grammar artifacts

Layer 4: consumers
  compiler frontend, interpreter, Tree-sitter adapter, shell execution, SDN API
  depend on dialect APIs; no grammar copies
```

### 19.2 Proposed paths

A conservative layout that avoids an immediate move of all current files:

```text
src/lib/common/parse/
  contracts.spl
  source_snapshot.spl
  origin_map.spl
  byte_classes.spl
  lex_state.spl
  token_arena.spl
  region_arena.spl
  syntax_unit_map.spl
  grammar_program.spl
  action_sink.spl
  cpu_work_table.spl
  mapping_graph.spl
  diagnostics.spl
  parser_service.spl
  incremental.spl

src/lib/common/parse/backends/
  scalar.spl
  simd.spl
  gpu.spl
  verify.spl

src/lib/compiler/simple_parse/
  dialect.spl
  actions_hir.spl
  actions_ast_compat.spl
  entry_rules.spl

src/lib/common/shell_parse/
  dialect.spl
  ast.spl
  actions.spl

src/lib/common/sdn/
  dialect.spl
  actions_value.spl
  ... existing public SDN APIs ...

src/compiler/10.frontend/
  cpu_reference_adapter.spl
  flat_ast_bridge.spl
  parsed_hir_adapter.spl
  frontend_service.spl
  legacy/
    parser_factory_compat.spl
    outline_parser_compat.spl
    partial_parser_compat.spl

src/generated/parse/
  ...
```

Repository naming/layer lint may choose a slightly different physical path. The
dependency direction is the binding requirement.

### 19.3 MDSOC dimensions

Feature dimension:

```text
source
encoding
lexical state
structure
tokens
syntax units
grammar
actions
HIR
global names
recovery
work table
incremental
verification
```

Layer/component dimension:

```text
contract
runtime
backend
dialect
consumer
tooling
test
```

A file should declare one primary feature and one layer. Cross-feature behavior uses
interfaces and mapping edges rather than duplicating scanner logic.

### 19.4 Refactor rule

Do not begin by moving files. Begin by:

1. adding contracts;
2. adding adapters around current files;
3. redirecting callers;
4. proving zero direct callers;
5. then moving/renaming.

This preserves bisectability and bootstrap stability.

---

## 20. Incremental and resident parsing

### 20.1 Snapshot edit model

```simple
struct SourceEdit:
    old_start_byte: u64
    old_end_byte: u64
    new_end_byte: u64
    inserted_buffer: BufferRef
```

An edit invalidates:

- overlapping classification blocks plus boundary carry;
- lexical-state chunks until summaries reconverge;
- affected opaque/structural regions;
- enclosing syntax units;
- dependent HIR/global-name requests.

### 20.2 Reconvergence

Lexical summaries permit early stop:

```text
recompute changed chunks
  -> compare exit summary with previous snapshot
  -> stop when state and masks reconverge
```

### 20.3 Tree-sitter correlation

Tree-sitter’s changed ranges and the compiler `SyntaxUnitMap` should be correlated by
source spans and stable feature/node IDs. Neither side must trust stale raw node handles
after an edit.

### 20.4 GPU resident workspace

Retain:

- normalized source pages;
- byte masks;
- token/region arenas;
- syntax units;
- Parsed HIR;
- global surface cache;
- mapping graph.

Evict by snapshot generation and memory budget. Device eviction must not invalidate the
CPU reference source or audit record.

---

## 21. Determinism, safety, and resource control

### 21.1 Deterministic allocation

Prefer:

```text
count -> scan -> emit
```

over global atomics for tokens, regions, HIR, tasks, diagnostics, and patches.

### 21.2 Bounds

Every grammar feature declares bounds or spill behavior for:

- lookahead;
- parser stack depth;
- local scratch;
- node count per unit;
- constraint count;
- custom block payload;
- nesting.

Exceeding a resource bound is not a syntax rejection. It creates a resource-spill task
or a configured fatal resource diagnostic.

### 21.3 Device failure

On launch/device failure:

- invalidate unpublished GPU output;
- retain snapshot and audit rows;
- select CPU reference or fail according to policy;
- never merge partially written arenas.

### 21.4 Grammar hash

Every buffer exchanged between CPU and GPU carries the same grammar/action hash.
Mismatches are fatal:

```text
gpu.fail.grammar_contract_mismatch
```

### 21.5 Security/untrusted input

For untrusted SDN, shell, or source input:

- validate encoding before grammar actions;
- enforce depth/node/size limits;
- reject integer/offset overflow;
- bound diagnostics and recovery attempts;
- do not execute custom block actions during parsing;
- separate parse from shell expansion/execution;
- fuzz every backend and cross-backend serializer.

---

## 22. Stage ownership and hard/fail mapping table

| Stage | GPU target | CPU SIMD | Permanent CPU authority | Temporary spill tags | Fatal tags |
|---|---|---|---|---|---|
| encoding selection | batch metadata | yes | policy/config lookup | `cpu.compat.encoding_codec:*` | invalid metadata |
| UTF-16/32/Latin-1 -> UTF-8 | yes | yes | no | unsupported codec | output overflow/invariant |
| UTF-8 validation | yes | yes | recovery/diagnostic on malformed input | none for supported encoding | validator disagreement |
| byte classification | yes | yes | no | unsupported dialect class | mask invariant |
| lexical-state scan | yes | yes | recovery if malformed | `gpu.hard.lex_state:*` | transition corruption |
| opaque-region map | yes | yes | recovery for unclosed text | custom unsupported | overlap/invariant |
| delimiter pairing | yes | yes | recovery for mismatch | special delimiter unsupported | pair invariant |
| indentation map | yes | yes | recovery for invalid indent | `gpu.hard.indent:*` | parent invariant |
| token boundaries | yes | yes | recovery for invalid token | Unicode/profile/custom token spill | overlapping tokens |
| token compaction | yes | yes | no | resource spill | arena corruption |
| syntax-unit mapping | yes | partial | recovery/compatibility if ambiguous | `gpu.hard.unit_boundary:*` | cyclic/invalid range |
| local parse | yes | scalar/table | recovery | `gpu.hard.rule:*` | parser VM invariant |
| Parsed-HIR emit | yes | scalar/table | no | `gpu.hard.action:*` | HIR arena invariant |
| local names | yes | CPU | no | temporary semantic spill | scope invariant |
| global names | request extraction | batching/hash | **yes** | n/a | patch mismatch |
| type constraints | yes | CPU vector/multicore | no | `gpu.hard.semantic:type*` | solver invariant |
| overload/trait selection | yes after CPU candidates | CPU | global candidate discovery only | semantic spill | inconsistent solution |
| DI/AOP/desugar | target yes | CPU | no | pass-specific spill | transformation invariant |
| syntax recovery | detection only | CPU | **yes** | n/a | recovery loop/contract |
| diagnostics format/order | detection metadata | CPU | final arbitration | none | invalid span |
| merge/commit | patch assist | CPU | transaction authority | none | conflict/hash mismatch |

The two bold rows are deliberate permanent CPU authorities. All other CPU work is
either placement for small inputs or tracked migration debt.

---

## 23. Verification strategy

### 23.1 Canonical comparison views

Backends may use different physical data, so tests compare canonical serializations.

#### Tokens

```text
kind
normalized start/end
original start/end
flags
text hash
```

#### Regions

```text
kind
bounds
parent
depth
```

#### Parsed HIR

```text
node kind
stable structural order
captured fields
symbolic name text/hash
source spans
flags
```

CPU AST output is converted to Parsed HIR for comparison.

#### Final HIR

Compare stable symbol/type IDs after canonical remapping, not allocator addresses.

#### Diagnostics

Compare:

```text
code
severity
original span
message template ID
arguments
suggestion edits
order
```

### 23.2 Corpus

- every repository `.spl`;
- every `.shs`;
- every `.sdn`;
- compiler bootstrap sources;
- standard library;
- examples;
- generated sources;
- positive feature corpus;
- negative/recovery corpus;
- Unicode/i18n corpus;
- custom/domain blocks;
- random grammar-generated programs;
- mutation-generated malformed programs.

### 23.3 Differential modes

```text
CPU reference vs CPU table
CPU reference vs CPU SIMD frontend
CPU reference vs GPU valid-source parse
CPU recovery vs GPU-detected + CPU-recovered path
Simple SDN vs Rust SDN
old shell parser vs ShellDialect
native Tree-sitter valid-code CST projection vs manifest feature map
```

### 23.4 Boundary testing

For each seed file, shift the source relative to SIMD/GPU chunk boundaries and test:

- every quote;
- every escape;
- every UTF-8 code point;
- every delimiter;
- every CR/LF pair;
- every multi-character operator;
- every indentation prefix.

### 23.5 Fuzzing

- byte fuzz for validators;
- token-preserving mutation;
- grammar-based generation;
- error-injection mutation;
- differential fuzz;
- incremental-edit fuzz;
- GPU resource-limit fuzz;
- work-table serialization fuzz.

### 23.6 Shadow mode

Before accelerated output is trusted:

```text
produce CPU reference result
produce accelerated result
compare
use CPU result
record mismatch task
```

Then graduate by corpus/feature to accelerated-primary with sampled reference checks.

---

## 24. CI and release gates

Suggested checks:

```text
check-parser-surface-parity.shs
check-grammar-generated-clean.shs
check-token-code-registry.shs
check-parser-cpu-reference-corpus.shs
check-parser-cpu-table-parity.shs
check-parser-simd-parity.shs
check-parser-gpu-parity.shs
check-parser-gpu-spill-ratchet.shs
check-parser-recovery-parity.shs
check-interpreter-parser-parity.shs
check-shell-parser-parity.shs
check-sdn-rust-simple-parity.shs
check-tree-sitter-node-query-parity.shs
check-parser-incremental-parity.shs
```

### Push-tier requirements

- generated artifacts clean;
- no parser surface missing from inventory;
- no new grammar divergence;
- no new `impl.todo.*`;
- CPU reference unit corpus;
- lightweight CPU table/SIMD parity;
- shell and SDN smoke parity.

### Bootstrap-tier requirements

- full CPU reference bootstrap;
- Stage 1/2/3 parser result parity;
- full compiler/interpreter corpus;
- Rust/Simple SDN bootstrap corpus.

### GPU CI requirements

A GPU-capable lane runs:

- all GPU-native feature tests;
- randomized batch sizes;
- strict zero-compat-spill mode for the admitted feature set;
- sampled full CPU comparison;
- device reset/failure tests;
- resident incremental tests.

GPU CI can be non-push-blocking initially, but no feature is marked `G0GpuNative` until
the lane is required for that feature.

### Release requirements

- full CPU reference build and tests;
- full GPU-verify corpus on supported devices;
- zero unexplained mismatches;
- zero `X0NeedsImplementation`;
- zero valid-corpus recovery tasks;
- spill baseline non-increasing;
- performance/memory receipts;
- native Tree-sitter corpus and query validation.

---

## 25. Performance and observability

### 25.1 Metrics

Per run and per stage:

```text
input bytes
normalized bytes
files/units
CPU/GPU time
transfer time
kernel launches
occupancy
temporary bytes
resident bytes
tokens
regions
HIR nodes
global-name requests
recovery tasks
compatibility spills by reason
verification samples/mismatches
cache hits
incremental invalidated bytes/units
```

### 25.2 Required latency metrics

- time to first diagnostic;
- time to first outline;
- time to first Parsed HIR;
- full frontend completion;
- CPU-global-name wait;
- recovery wait;
- incremental edit latency.

### 25.3 Bottleneck attribution

Every `BackendReceipt` records:

```text
placement decision
selected backend per stage
bytes processed
task counts
spill reason counts
largest unit
slowest unit/rule
arena high-water marks
```

This makes parser performance debuggable by grammar feature rather than only by total
compile time.

### 25.4 Admission criteria

Do not declare GPU success from a synthetic GB/s scanner benchmark alone. Admission
requires end-to-end measurements including:

- transfers;
- global-name round trip;
- task-table handling;
- HIR output;
- verification overhead;
- memory footprint;
- small-file regressions.

---

## 26. Staged implementation plan

Each phase is independently mergeable and retains the CPU reference path.

### Phase 0 — freeze behavior and inventory surfaces

**Goal:** establish a trustworthy baseline before refactoring.

Tasks:

- `GPU-PARSE-0001` Record the baseline commit and toolchain.
- `GPU-PARSE-0002` Serialize current compiler tokens, flat AST, rich AST, HIR, and
  diagnostics canonically.
- `GPU-PARSE-0003` Inventory every parser/lexer/splitter surface.
- `GPU-PARSE-0004` Build positive/negative grammar feature corpus.
- `GPU-PARSE-0005` Build shell token/execution corpus.
- `GPU-PARSE-0006` Build Rust/Simple SDN corpus.
- `GPU-PARSE-0007` Add grammar-surface parity report.
- `GPU-PARSE-0008` Add initial push gate.

Exit criteria:

- complete surface inventory;
- reproducible CPU reference receipts;
- no undocumented parser entry point;
- current bootstrap green.

### Phase 1 — contracts, mapping, and CPU work table

**Goal:** introduce common data contracts without changing accepted syntax.

Tasks:

- `GPU-PARSE-0101` Add `SourceSnapshot` and normalized byte-span contract.
- `GPU-PARSE-0102` Add `OriginMap`.
- `GPU-PARSE-0103` Add token/region/syntax-unit canonical views.
- `GPU-PARSE-0104` Add `CpuWorkTable`.
- `GPU-PARSE-0105` Add `MappingGraph`.
- `GPU-PARSE-0106` Add `ParserService` and backend receipt.
- `GPU-PARSE-0107` Wrap current parser as `CpuReferenceBackend`.
- `GPU-PARSE-0108` Add audit CLI.

Exit criteria:

- all existing compiler parse calls can pass through an adapter;
- CPU output unchanged;
- work table serializes deterministically;
- no GPU code required.

### Phase 2 — parser and lexer context refactor

**Goal:** make the CPU reference parser reentrant and safe for parallel/shadow parsing.

Tasks:

- `GPU-PARSE-0201` Move source/cursor state to `LexerContext`.
- `GPU-PARSE-0202` standardize UTF-8 byte spans;
- `GPU-PARSE-0203` move indentation/delimiter state;
- `GPU-PARSE-0204` move parser cursor/lookahead state;
- `GPU-PARSE-0205` move scope/declaration scratch;
- `GPU-PARSE-0206` remove environment-based parser state from normal path;
- `GPU-PARSE-0207` support module/declaration/statement/expression entry rules;
- `GPU-PARSE-0208` retain compatibility shims until zero callers.

Each task must run:

```text
targeted tests
whole parser corpus
whole compiler compile
bootstrap stage tests
```

Exit criteria:

- two files can parse concurrently;
- interpreter-callable parser context;
- byte spans correct for Unicode;
- canonical CPU output unchanged.

### Phase 3 — canonical grammar manifests and generators

**Goal:** establish one normative grammar per dialect.

Tasks:

- `GPU-PARSE-0301` Define grammar schema.
- `GPU-PARSE-0302` Extract `simple.sdn` feature-by-feature from the CPU reference.
- `GPU-PARSE-0303` Extract `shell.sdn`.
- `GPU-PARSE-0304` reconcile and extract `sdn.sdn`;
- `GPU-PARSE-0305` assign stable token/rule/action IDs;
- `GPU-PARSE-0306` generate feature inventory;
- `GPU-PARSE-0307` generate CPU/GPU metadata skeletons;
- `GPU-PARSE-0308` add stale-generation gate;
- `GPU-PARSE-0309` add bootstrap-safe generator path.

Exit criteria:

- every grammar feature has a manifest ID;
- every parser surface reports support;
- no generated-artifact drift;
- CPU reference remains independent.

### Phase 4 — consumer unification

**Goal:** eliminate public grammar forks before acceleration.

#### Compiler

- route all frontends through `ParserService`;
- keep flat-AST bridge;
- add Parsed-HIR comparison adapter.

#### Interpreter

- verify current parser-module resolution;
- shadow with `ParserService`;
- migrate module/statement/expression entry points.

#### Shell

- introduce lossless `ShellToken` and `ShellWordPart`;
- replace pipeline/word/redirect duplicate scanners;
- migrate control-flow parser.

#### SDN

- implement shared-runtime `SdnDialect`;
- retain Rust bootstrap oracle;
- unify spans/issues/event sink.

Exit criteria:

- consumers call shared contracts;
- old parsers remain only as explicit compatibility backends;
- grammar changes cannot be made in consumer code.

### Phase 5 — native Tree-sitter

**Goal:** replace misleading naming and add real incremental editor parsing.

Tasks:

- `GPU-PARSE-0501` Rename handwritten outline component.
- `GPU-PARSE-0502` Generate/add native `tree-sitter-simple`.
- `GPU-PARSE-0503` Add external scanner for indentation/custom blocks.
- `GPU-PARSE-0504` generate/check node mapping;
- `GPU-PARSE-0505` validate queries;
- `GPU-PARSE-0506` implement edit/old-tree/changed-range flow;
- `GPU-PARSE-0507` derive outline from CST or syntax-unit map;
- `GPU-PARSE-0508` retire independent outline grammar after parity.

Exit criteria:

- valid Simple corpus parses in native Tree-sitter;
- incremental changed ranges work;
- outline feature parity;
- current heuristic fallback is explicitly named and isolated.

### Phase 6 — CPU SIMD frontend

**Goal:** produce shared masks/tokens/regions efficiently on CPU.

Tasks:

- `GPU-PARSE-0601` Add scalar `ByteClassArena` reference.
- `GPU-PARSE-0602` Extend SIMD runtime ABI.
- `GPU-PARSE-0603` AVX2 fused classifier.
- `GPU-PARSE-0604` AArch64 NEON fused classifier.
- `GPU-PARSE-0605` quote/escape/comment masks;
- `GPU-PARSE-0606` structural and indentation maps;
- `GPU-PARSE-0607` token count/scan/emit;
- `GPU-PARSE-0608` Unicode identifier slow lane;
- `GPU-PARSE-0609` runtime dispatch and cost model;
- `GPU-PARSE-0610` compare/benchmark `simdutf` transcoding.

Exit criteria:

- exact scalar parity;
- no new source rescans without a measured reason;
- no regression for tiny input;
- parser uses shared token/region contracts.

### Phase 7 — GPU lexical and structural frontend

**Goal:** GPU from encoding through syntax-unit map.

Tasks:

- `GPU-PARSE-0701` portable GPU primitive API: scan/select/sort/segmented scan.
- `GPU-PARSE-0702` source batching and arenas.
- `GPU-PARSE-0703` UTF transcode kernels.
- `GPU-PARSE-0704` fused validation/classification.
- `GPU-PARSE-0705` lexical transition summaries and scan.
- `GPU-PARSE-0706` opaque-region map.
- `GPU-PARSE-0707` delimiter pairing.
- `GPU-PARSE-0708` indentation hierarchy.
- `GPU-PARSE-0709` token count/scan/emit.
- `GPU-PARSE-0710` syntax-unit mapper.
- `GPU-PARSE-0711` work-table device emission.
- `GPU-PARSE-0712` GPU/CPU mask and token differential suite.

Exit criteria:

- all admitted valid corpus reaches exact Token/Region/Unit parity;
- every unsupported feature emits a stable task;
- no silent file fallback;
- transfer and memory receipts available.

### Phase 8 — GPU local parser and Parsed HIR

**Goal:** direct GPU parse of mapped units.

Tasks:

- `GPU-PARSE-0801` GrammarProgram VM.
- `GPU-PARSE-0802` ActionProgram VM.
- `GPU-PARSE-0803` declaration/header parser.
- `GPU-PARSE-0804` statement parser.
- `GPU-PARSE-0805` Pratt/type/pattern parsers.
- `GPU-PARSE-0806` count/scan/emit HIR.
- `GPU-PARSE-0807` local scopes and local names.
- `GPU-PARSE-0808` global-name request extraction.
- `GPU-PARSE-0809` AST compatibility adapter.
- `GPU-PARSE-0810` strict zero-spill coverage tests.

Exit criteria:

- Parsed-HIR canonical parity for admitted valid features;
- no pointer-rich GPU AST requirement;
- deterministic HIR IDs;
- all hard rules visible in work table.

### Phase 9 — CPU global names and recovery integration

**Goal:** complete the production hybrid transaction.

Tasks:

- `GPU-PARSE-0901` GlobalNameRequest schema and transfer.
- `GPU-PARSE-0902` CPU module/import/visibility resolver adapter.
- `GPU-PARSE-0903` stable name patch stream.
- `GPU-PARSE-0904` recovery request adapter to current CPU parser.
- `GPU-PARSE-0905` recovery patch and partial-node bridge.
- `GPU-PARSE-0906` escalation scheduler.
- `GPU-PARSE-0907` deterministic merge/commit.
- `GPU-PARSE-0908` work audit and ratchet gate.
- `GPU-PARSE-0909` malformed corpus parity.

Exit criteria:

- valid corpus uses CPU only for global names;
- malformed corpus diagnostics match reference;
- no patch conflicts;
- fallback granularity recorded.

### Phase 10 — GPU semantic continuation

**Goal:** resume GPU work after names are patched.

Tasks:

- constraint graph;
- type unification;
- overload/trait selection from CPU candidate sets;
- generics;
- effect/capability checks;
- DI/AOP transforms;
- desugaring;
- downstream HIR/MIR adapter;
- per-pass work tags and parity.

Exit criteria:

- each admitted pass has canonical output parity;
- compatibility spill baseline decreases;
- CPU global names and recovery remain the only permanent authorities.

### Phase 11 — resident and incremental mode

**Goal:** make offload worthwhile for whole workspaces and repeated edits.

Tasks:

- resident arena cache;
- edit invalidation/reconvergence;
- Tree-sitter changed-range correlation;
- module-surface cache;
- GPU memory eviction;
- incremental verification;
- compiler-daemon integration.

Exit criteria:

- unchanged units reused safely;
- incremental results equal full parse;
- bounded memory;
- measured latency benefit.

---

## 27. Work-item implementation backlog

The following table should seed project tracking. `Hard tag` is the runtime tag that
makes unfinished work discoverable.

| ID | Deliverable | Dependency | Hard tag until done | Completion evidence |
|---|---|---|---|---|
| PRT-001 | parser-surface inventory | none | `grammar.divergence.surface:*` | generated inventory + gate |
| PRT-002 | CPU canonical token serializer | PRT-001 | `impl.todo.verify.tokens` | stable corpus hashes |
| PRT-003 | CPU AST->ParsedHIR canonicalizer | PRT-002 | `impl.todo.verify.hir` | CPU self-roundtrip |
| PRT-004 | `SourceSnapshot`/`OriginMap` | PRT-002 | `impl.todo.origin_map` | Unicode/encoding span tests |
| PRT-005 | `CpuWorkTable` | PRT-004 | `impl.todo.work_table` | deterministic SDN audit |
| PRT-006 | `ParserService` | PRT-004 | `impl.todo.parser_service` | all current calls adapted |
| PRT-007 | reentrant lexer | PRT-006 | `gpu.hard.legacy_global_lexer` | parallel parse test |
| PRT-008 | reentrant parser | PRT-007 | `gpu.hard.legacy_global_parser` | entry-rule tests |
| GRM-001 | grammar schema | PRT-001 | `impl.todo.grammar_schema` | schema validation |
| GRM-002 | Simple manifest | GRM-001 | `grammar.divergence.compiler_reference:*` | full feature coverage |
| GRM-003 | Shell manifest | GRM-001 | `grammar.divergence.shell:*` | shell corpus |
| GRM-004 | SDN manifest | GRM-001 | `grammar.divergence.sdn_*:*` | Rust/Simple parity |
| GRM-005 | stable token/rule IDs | GRM-002..4 | `impl.todo.grammar_ids` | no unversioned changes |
| TSR-001 | rename legacy outline | PRT-001 | `grammar.divergence.outline:*` | zero misleading API names |
| TSR-002 | native Tree-sitter grammar | GRM-002 | `impl.todo.tree_sitter_grammar` | valid corpus |
| TSR-003 | external scanner | TSR-002 | `gpu.hard.tree_sitter_external:*` | indent/custom block tests |
| TSR-004 | query/node gate | TSR-002 | `grammar.divergence.tree_sitter:*` | query compile tests |
| INT-001 | interpreter shadow parser | PRT-006, GRM-002 | `grammar.divergence.interpreter:*` | parse/eval parity |
| SHL-001 | lossless shell tokens | GRM-003 | `grammar.divergence.shell.quote` | quote corpus |
| SHL-002 | unified pipeline/redirect AST | SHL-001 | `grammar.divergence.shell.pipeline` | execution parity |
| SHL-003 | control-flow migration | SHL-002 | `grammar.divergence.shell.control` | script corpus |
| SDN-001 | SDN feature-difference report | GRM-004 | `grammar.divergence.sdn_*:*` | decided matrix |
| SDN-002 | shared SDN event parser | SDN-001 | `impl.todo.sdn_event_parser` | values/spans/issues parity |
| SIMD-001 | scalar mask reference | PRT-004 | `impl.todo.byte_masks` | exhaustive mask tests |
| SIMD-002 | AVX2 classifier | SIMD-001 | `impl.todo.simd.avx2` | exact parity + benchmark |
| SIMD-003 | NEON classifier | SIMD-001 | `impl.todo.simd.neon` | exact parity + benchmark |
| SIMD-004 | quote/comment/structure masks | SIMD-002/3 | `impl.todo.simd.lex_state` | boundary matrix |
| GPU-001 | GPU batch/arena runtime | PRT-005 | `impl.todo.gpu.runtime` | allocation/failure tests |
| GPU-002 | GPU UTF/classifier | GPU-001, SIMD-001 | `impl.todo.gpu.utf8` | scalar parity |
| GPU-003 | GPU lexical-state scan | GPU-002 | `gpu.hard.lex_state:*` | cross-chunk corpus |
| GPU-004 | GPU delimiters/indent | GPU-003 | `gpu.hard.indent:*` | region parity |
| GPU-005 | GPU tokens | GPU-004 | `impl.todo.gpu.tokens` | token parity |
| GPU-006 | syntax-unit map | GPU-005, GRM-002 | `gpu.hard.unit_boundary:*` | unit parity |
| GPU-007 | grammar/action VM | GPU-006 | `gpu.hard.rule:*` | rule coverage |
| GPU-008 | Parsed-HIR emit | GPU-007 | `gpu.hard.action:*` | HIR parity |
| GPU-009 | local symbols | GPU-008 | `gpu.hard.semantic.local_name` | scope corpus |
| CPU-001 | global-name request/patch | GPU-009 | `cpu.required.global_name` | project corpus |
| CPU-002 | recovery request/patch | GPU-007 | `cpu.required.error_recovery` | invalid corpus |
| GPU-010 | semantic continuation | CPU-001 | `gpu.hard.semantic:*` | pass-by-pass parity |
| RES-001 | resident incremental arenas | GPU-010 | `impl.todo.gpu.resident` | incremental parity |
| GATE-001 | spill ratchet | PRT-005 | `impl.todo.gate.spill` | CI enforcement |
| GATE-002 | generated grammar parity | GRM-005 | `impl.todo.gate.grammar` | clean regeneration |
| GATE-003 | all-backend differential gate | GPU-008 | `impl.todo.gate.differential` | release receipt |

---

## 28. Acceptance criteria

The project is complete for the first production GPU-hybrid release when:

1. `cpu-reference` compiles and tests the complete language without GPU/SIMD.
2. `cpu-simd` is canonically equivalent to `cpu-reference`.
3. GPU normalization, validation, masks, tokens, regions, and unit maps match the CPU
   reference for the complete admitted valid corpus.
4. GPU local parsing and Parsed HIR match the canonical CPU conversion.
5. GPU resolves all local names.
6. CPU global-name requests and patches are deterministic and cached.
7. CPU recovery reproduces reference diagnostics and partial-tree behavior.
8. Valid admitted source produces no recovery task.
9. Every non-native GPU case has a stable tagged work row.
10. No `X0NeedsImplementation` row exists in release corpus.
11. No untagged fallback exists.
12. Compiler and interpreter accept the same Simple grammar for shared entry rules.
13. Shell quote/pipeline/redirect/control-flow logic uses one dialect parser.
14. Rust and Simple SDN pass one canonical feature corpus.
15. Native Tree-sitter parses all valid Simple corpus and query mappings are current.
16. Incremental results equal full reparse for admitted resident mode.
17. Performance and memory receipts include transfers and CPU authority time.
18. The accelerated path can be disabled with one supported configuration switch.

The long-term “only two CPU authorities” target is reached when every compatibility
spill outside:

```text
cpu.required.global_name*
cpu.required.error_recovery*
```

has been eliminated for the complete supported grammar and semantic pipeline.

---

## 29. Immediate first pull requests

To minimize risk, the first changes should be:

### PR 1 — parser surface inventory and naming correction

- add the parser-surface inventory;
- rename the current handwritten TreeSitter outline facade to a legacy/outline name;
- add compatibility aliases;
- no parser behavior change.

### PR 2 — canonical comparison receipts

- token serializer;
- flat/rich AST serializer;
- AST-to-Parsed-HIR comparison form;
- diagnostics serializer;
- whole repository corpus receipts.

### PR 3 — `ParserService` and CPU reference adapter

- introduce request/result contracts;
- route one low-risk compiler entry point;
- retain all existing parser code;
- add `--frontend=cpu-reference`.

### PR 4 — CPU work table and audit CLI

- define task schema/tags;
- serialize deterministic `frontend_work.sdn`;
- add a no-untagged-fallback assertion;
- initially record only synthetic/self-test tasks.

### PR 5 — grammar divergence gate

- add feature IDs;
- inventory compiler, outline, partial, interpreter, shell, and SDN surfaces;
- fail on unregistered additions;
- do not generate a new parser yet.

Only after these foundations should parser-state refactoring or GPU kernels begin.

---

## 30. Final architectural rules

1. **The language is not the parser implementation.** The dialect manifest and language
   specification define syntax; implementations prove parity.
2. **The CPU reference parser is never removed.**
3. **A GPU failure is data, not a hidden branch.** It becomes a work-table row.
4. **Function/statement/expression mapping is structural indexing, not parsing.**
5. **Parsed HIR may contain symbolic global references.** That is expected.
6. **Global names are CPU authority; local names are GPU work.**
7. **Recovery is CPU authority; GPU detection and localization are GPU work.**
8. **All other CPU compatibility work is temporary debt with a stable tag.**
9. **One shared runtime supports multiple dialects.** It does not erase language
   differences.
10. **Tree-sitter is an incremental editor parser, not the compiler oracle.**
11. **Shell parsing and shell expansion/execution are separate phases.**
12. **SDN bootstrap independence is retained until generated/shared parity is proven.**
13. **UTF-8 byte offsets are canonical; original-encoding positions are mapped.**
14. **Count/scan/emit is the default deterministic GPU allocation pattern.**
15. **A grammar change must update and test every affected surface in one change.**
16. **No benchmark claim is accepted without end-to-end Simple measurements.**

---

## 31. References

### Repository evidence

- `src/compiler/10.frontend/core/parser.spl`
- `src/compiler/10.frontend/core/lexer.spl`
- `src/compiler/10.frontend/parser_factory.spl`
- `src/compiler/10.frontend/parser_types.spl`
- `src/compiler/10.frontend/flat_ast_bridge.spl`
- `src/compiler/10.frontend/treesitter.spl`
- `src/compiler/10.frontend/treesitter/outline.spl`
- `src/compiler/10.frontend/parser/partial.spl`
- `src/compiler/10.frontend/parser/recovery.spl`
- `src/app/interpreter/parser_pure.spl`
- `src/os/apps/shell/shell_script.spl`
- `src/os/apps/shell/shell_pipe.spl`
- `src/os/apps/shell/shell_redirect.spl`
- `src/lib/common/sdn/lexer.spl`
- `src/lib/common/sdn/parser.spl`
- `src/compiler_rust/sdn/src/lexer.rs`
- `src/compiler_rust/sdn/src/parser.rs`
- `src/lib/encoding/simd_text_sffi.spl`
- `src/runtime/runtime_simd_utf8.c`
- `spec/compiler_schema/registry/compiler.frontend.Grammar.sdn`
- `doc/09_report/2026/02/parser_unification_phase1_3_complete_2026-02-09.md`

Repository: <https://github.com/ormastes/simple>  
Audited commit: <https://github.com/ormastes/simple/commit/1b12bd36bc8388d5c237da0f2f8ee2af7668f0ae>

### Primary external references

- Elias Stehle and Hans-Arno Jacobsen, “ParPaRaw: Massively Parallel Parsing of
  Delimiter-Separated Raw Data,” PVLDB 13(5), 2020.  
  <https://arxiv.org/abs/1905.13415>
- simdutf documentation and source.  
  <https://simdutf.github.io/simdutf/>  
  <https://github.com/simdutf/simdutf>
- NVIDIA CCCL/CUB `DeviceScan` documentation.  
  <https://nvidia.github.io/cccl/cub/api/structcub_1_1DeviceScan.html>
- Tree-sitter, “Advanced Parsing.”  
  <https://tree-sitter.github.io/tree-sitter/using-parsers/3-advanced-parsing.html>
- Tree-sitter, “The Grammar DSL.”  
  <https://tree-sitter.github.io/tree-sitter/creating-parsers/2-the-grammar-dsl.html>
- Unicode Standard Annex #31, “Unicode Identifiers and Syntax.”  
  <https://www.unicode.org/reports/tr31/>
- simdjson design notes.  
  <https://github.com/simdjson/simdjson/blob/master/HACKING.md>
- Pison structural-index implementation and paper references.  
  <https://github.com/AutomataLab/Pison>

### Research interpretation

ParPaRaw demonstrates that chunk-local finite-state summaries can be composed without a
preliminary serial context pass for its data-parsing workload. This design applies the
same general technique to lexical states, but does not assume ParPaRaw’s reported
throughput transfers directly to a programming-language parser.

simdjson and Pison demonstrate the value of separating structural indexing from later
structure/value construction. Simple extends that principle with indentation,
declaration/statement unit maps, direct Parsed-HIR actions, and an explicit CPU work
table.

CUB’s scan contract reinforces the central implementation rule: transition composition
and allocation scans must use truly associative, integer/discrete operators. Floating
point or pseudo-associative operations must not participate in parser identity or
ordering.

Tree-sitter’s old-tree/edit/reparse model is used only for editor incremental parsing.
Compiler correctness remains independently verified by the CPU reference parser and the
canonical grammar feature corpus.
