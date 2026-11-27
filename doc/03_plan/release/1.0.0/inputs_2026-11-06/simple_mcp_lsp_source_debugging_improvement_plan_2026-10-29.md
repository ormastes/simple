# Simple MCP/LSP: intent-based source views and unified debugging
## Design and incremental implementation plan for Simple, SDN, SHS, and external languages

**Date:** 2026-10-29 (Asia/Seoul)  
**Document revision:** 1.0 — a design revision, not a deployed protocol version  
**Repository:** `ormastes/simple`  
**Inspected baseline:** `main` at `e93e2a7bed8d576ad81ec7d51e3d64c2338464f3`  
**Baseline commit date:** 2026-10-27; inspection performed on 2026-10-29  
**Implementation branch:** Configurable; recheck every integration point on the selected branch before coding.  
**Status:** Proposed implementation plan grounded in scoped source inspection. No repository code was changed, and no Simple build, live MCP/LSP session, or repository test suite was executed for this document.

> **Decision:** Build one reusable, snapshot-aware source-inspection and projection service. Simple MCP, LSP-MCP, LSP, the debugging screen, and the shared REPL/debugger consume it. Simple/SDN/SHS reuse their native parsing and semantic infrastructure; other languages receive Tree-sitter structural views and optional language-server/compiler-backed semantics. Preserve one authoritative `DebugServiceV1` for mutable debug sessions.

The source view is a **projection**, not an edited source file. A syntax tree is not a complete semantic analysis. A registered tool is not proof of working behavior. A stopped execution is not interchangeable with a dump, and a suggested fix is not proof of correctness.

## Contents

1. [Requirements and fixed decisions](#1-requirements-and-fixed-decisions)
2. [Inspected baseline and concrete gaps](#2-inspected-baseline-and-concrete-gaps)
3. [Architecture and ownership](#3-architecture-and-ownership)
4. [Language providers](#4-language-providers)
5. [Snapshots, positions, and shared caches](#5-snapshots-positions-and-shared-caches)
6. [Agent-session preferences](#6-agent-session-preferences)
7. [Source-view examples and folding](#7-source-view-examples-and-folding)
8. [Compact help and navigation](#8-compact-help-and-navigation)
9. [Annotations, hints, and detail expansion](#9-annotations-hints-and-detail-expansion)
10. [Diagnostics and safe automatic fixes](#10-diagnostics-and-safe-automatic-fixes)
11. [Source analysis for debugging](#11-source-analysis-for-debugging)
12. [Debugging screen and shared REPL integration](#12-debugging-screen-and-shared-repl-integration)
13. [Environment and configuration analysis](#13-environment-and-configuration-analysis)
14. [Recent changes and regression analysis](#14-recent-changes-and-regression-analysis)
15. [MCP, LSP-MCP, LSP, and Neovim contracts](#15-mcp-lsp-mcp-lsp-and-neovim-contracts)
16. [Editing and replacement transactions](#16-editing-and-replacement-transactions)
17. [Performance and resource controls](#17-performance-and-resource-controls)
18. [Security and operational safety](#18-security-and-operational-safety)
19. [Incremental delivery and ownership](#19-incremental-delivery-and-ownership)
20. [Acceptance tests and release gates](#20-acceptance-tests-and-release-gates)
21. [Experiments and measurable outcomes](#21-experiments-and-measurable-outcomes)
22. [Migration checklist and risk register](#22-migration-checklist-and-risk-register)
23. [References and evidence](#23-references-and-evidence)

---

## 1. Requirements and fixed decisions

This document consolidates the full source-analysis/viewer discussion and connects it to the earlier shared REPL/debugger plan [C01]. All new command names, configuration keys, contracts, and module paths below are proposals unless explicitly identified as inspected source.

| ID | Requirement / decision |
|---|---|
| R01 | Cover Simple `.spl`, SDN `.sdn`, and SHS `.shs` as first-class source/configuration/script views. |
| R02 | Provide the same structural viewing model for C/C++, Rust, Python, and additional registered Tree-sitter languages. |
| R03 | Reuse native Simple parser/compiler/query infrastructure. Do not write competing parsers, type checkers, or debug evaluators in MCP handlers. |
| R04 | First successful code open per agent or subagent shows Essential help once. Later opens show only the compact help footer. |
| R05 | Line numbers are **OFF by default**. `num` toggles them; preferences persist for the entire logical agent session. |
| R06 | Each subagent has independent preferences, help state, current view, and navigation history. Transport connections are not agent identities. |
| R07 | A file open without a target/intent returns a bounded structural outline with all bodies folded, not the full file. |
| R08 | Navigation opens the target and necessary enclosing context; unrelated bodies remain folded. This does not close human editor buffers/windows. |
| R09 | Imports/includes/use declarations and other relevant non-block statements have synthetic fold groups with accurate source ranges. |
| R10 | Generated end-of-line information starts after **`▌`** in Unicode mode; ASCII decoration mode uses **`\|`**. |
| R11 | Optional in-code type/parameter hints may use display-only `/* ... */`; raw source and edit payloads never contain generated hints. |
| R12 | Default footer is `[ess] [adv]`, not a toolbar repeated on every source line. Display preferences and advanced commands are available through help. |
| R13 | Show concise errors, warnings, relevant recent changes, and active debug information. Expand explanations, types, provenance, diffs, and fixes on demand. |
| R14 | Compiler/linter automatic fixes use canonical diagnostics and revision-checked edit transactions, with preview and explicit safety classification. |
| R15 | Support callers/callees, reference/read/write classification, types, control flow, data flow, aliases, state changes, slices, and change impact, with capability and completeness labels. |
| R16 | Distinguish static possible writers from runtime observed writers. Never invent write history that was not recorded. |
| R17 | Generate SDN environment/configuration observations and explain actual settings, selected tools, overrides, containers, OS/target identity, and build provenance. |
| R18 | Support recent changes over a default seven-day window or a specified date/ref/tag range, resolved to reproducible boundaries. |
| R19 | Integrate the same source view into the Simple debugging screen, REPL, DAP, MCP, test runner, assertion handling, and dump inspection. |
| R20 | Preserve the earlier order: test stop/tunnel → shared debugging/MCP → sassert/dumps/server → interpreter replacement → native replacement [C01]. |
| R21 | Keep expensive analysis lazy and bounded. Return explicit partial/unsupported/error states, not empty-success placeholders. |
| R22 | Make all behavior testable through real public interfaces and modern SSpec acceptance specifications. |

### 1.1 Non-goals for the first releases

Do not implement a full Vim clone, a universal interprocedural verifier, a universal cross-language debugger, automatic production repair/deployment, or arbitrary native class-layout migration. Do not intercept every external agent's filesystem tool implicitly. Provide explicit integrations and preserve raw reading/editing contracts.

### 1.2 Terminology

**Source snapshot** is immutable original text plus identity. **Projection** is a selected and decorated rendering. **Annotation** is a separately stored fact attached to a source range. **View session** belongs to an agent/client. **Debug session** belongs to `DebugServiceV1`. **Stop epoch** identifies one stopped execution state. These identities must never be overloaded into one ambiguous `session_id`.

## 2. Inspected baseline and concrete gaps

### 2.1 Evidence standard

The following table records what inspected source establishes, not an end-to-end certification. The inspected SHA is dated October 27, not October 29. Earlier conversation descriptions of “supported,” “missing,” or “active” are superseded where this inspection provides more precise evidence.

| Area | Observed source evidence | Plan consequence |
|---|---|---|
| Main source reader | `main_lazy_diag_tools.spl` implements `simple_read`: reads the file, prefixes every line with a number, runs `simple check`, and appends diagnostic text. Empty content is treated as a read failure [R-SRC]. | Add a snapshot/projection service and explicit compatibility profile. Fix empty-file handling. Do not run compilation on every navigation read. |
| Diagnostic extraction | The same module parses textual `path:line:col` output and labels exit-code zero as clean [R-SRC]. | Prefer canonical structured diagnostics. Test Windows drive paths, warnings on successful builds, failed analyzer execution, and missing output. |
| LSP-MCP entry | `simple_lsp_mcp/main.spl` advertises 13 tools: definition, references, hover, symbols, visibility, diagnostics, completion, type-at, signature help, implementation, highlights, type definition, SAML analysis [R-LMCP]. | Preserve these tools and add shared-source/analysis parity. The inspected list does not expose the full proposed viewer, fix, or debugging analysis surface. |
| LSP entry | `src/app/lsp/main.spl` delegates to the shared standard-library server loop [R-LSPENTRY]. | Keep the app thin. Add protocol work in the shared implementation, not a new app-specific engine. |
| LSP dispatch | The loop routes call hierarchy, inlay hints, code actions, pull diagnostics, folding, semantic tokens, and core navigation [R-LSPLOOP]. | These features are not all absent; check each handler and query producer separately. |
| Call hierarchy | `lsp_handle_incoming_calls` and `lsp_handle_outgoing_calls` unconditionally return empty arrays in the inspected handler. Preparation derives a name from hover output [R-LSPHAND]. | Implement resolved call edges and honest capabilities. Empty arrays cannot stand for an unimplemented query. |
| Hints/folding | Handlers invoke query commands for inlay hints and folding [R-LSPHAND]. | Reuse and validate these paths, then remove repeated process launch/parsing where practical. |
| Code actions | The handler invokes `code-actions`; its conversion scans serialized JSON, reconstructs edits using the request URI, emits `version: null`, and requires nonempty `newText` to build edits [R-ACTIONS]. | Test/fix deletion edits, multiple replacements/files, URI preservation, nested JSON, and stale-buffer protection. A valid deletion has empty replacement text. |
| Diagnostic schema | `DiagnosticV1` schema includes stable codes, labels across files, child diagnostics, macro traces, replacements, and `safe/likely/uncertain` confidence. That lane explicitly excludes LSP/SARIF rendering [R-DIAG]. | Extend/adapt the existing schema rather than creating another diagnostic/fix model. |
| MCP debug handler file | `main_lazy_debug_tools.spl` contains synthetic `main:1` stack output, empty variables, an expression echoed as a string result, and control responses without demonstrated target execution in those functions [R-MCPDBG]. | Audit dispatch for each shipping executable, then route admitted operations to a real service/backend or return unsupported. Do not infer all native adapters behave this way. |
| Central debug service | `service_v1.spl` explicitly owns session/authorization bookkeeping and does not itself talk to targets [R-DBGSVC]. | Preserve service authority; add/complete backend routing through the existing architecture. |
| Debug architecture | The integration index selects central ownership and warns that source presence/command parsing is not live support [R-DBGARCH]. | Keep capability receipts and real execution tests as release evidence. |
| Simple outline facility | `compiler/10.frontend/treesitter.spl` is a façade over token-based and heuristic outline modules [R-OUTLINE]. | Reuse it as an outline provider. Its name alone does not prove generated upstream Tree-sitter grammar compatibility. |
| SDN normalization | `parse_dialect_adapters_v1.spl` uses the SDN parser, spans, issues, and canonical encoding; comments identify a sosh adapter/type-name collision blocker [R-DIALECT]. | Reuse source spans and verify the blocker on the implementation branch; canonical encoding must not replace the lossless source view. |
| SHS dialects | Inspected search results include `.shs` scripts with `#!/bin/sh` and `#!/usr/bin/env bash` [R-SHS1], [R-SHS2]. | Resolve dialect from explicit configuration, language ID, shebang, and source evidence; extension alone is insufficient. |
| Host configuration | `config/host/host_config.sdn` documents host defaults and precedence, including consumer-specific overrides [R-HOST]. | Explain the existing owner's precedence; do not silently impose a new universal precedence. |
| Build environment | `native_build_environment_identity.spl` lists build-relevant environment variables and digest infrastructure [R-ENV]. | Reuse environment identity for analysis/cache/build comparison, adding explainable provenance and redaction. |

### 2.2 First audit deliverable

Produce `capability_audit.sdn` with one row per **frontend × operation × language × backend × build profile**. Track `declared`, `routed`, `provider_implemented`, `tested`, `runtime_admitted`, and evidence references separately. Include bootstrap/release variants and feature-disabled builds. A function body, mock test, documentation claim, or registered MCP tool alone does not qualify as runtime admission.

Prioritize these concrete defects: empty call-hierarchy success; raw reader's forced numbers/full-file output; false “clean” status; deletion/multi-file/version handling in code actions; synthetic debug results; ambiguous agent-global requester state; and missing dialect-specific admission.

## 3. Architecture and ownership

### 3.1 Shared services, thin frontends

```text
Editor buffers / worktree / SCV snapshot / generated source / dump source
                               |
                  SourceSnapshotStore + position maps
                               |
          +--------------------+----------------------+
          |                    |                      |
  Simple compiler         SDN / SHS             External languages
  AST / HIR / MIR       native providers       Tree-sitter + optional LSP
          +--------------------+----------------------+
                               |
               SourceAnalysisService / QueryPlanner
        symbols, calls, types, effects, diagnostics, provenance
                               |
                SourceProjectionService + ViewSession
            selection, folds, annotation detail, bounded output
                               |
       +-------------+---------+---------+--------------+
       |             |                   |              |
   Simple MCP    LSP-MCP/LSP          Neovim bridge   Debug screen/REPL
       |             |                   |              |
       +-------------+-------------------+--------------+
                               |
          DebugServiceV1: session authority, policy, receipts
                               |
       interpreter | native adapters | test-worker tunnel | dump adapter
```

`EnvironmentInspector` and `ConfigProvenanceService` supply the semantic and runtime context. `ChangeIndex` supplies committed/worktree history. The build/test runner and SCV cache supply immutable artifacts and dependency invalidation. The source service may **read** debug snapshots through the debug service; it must not own an independent resume/step/watchpoint mechanism.

### 3.2 Logical library boundaries

The following are proposed module families, to be placed under the repository's approved common/nogc hierarchy after dependency review:

| Module family | Owns | Must not own |
|---|---|---|
| `source/contracts` | Snapshot/range/symbol/view/annotation/capability contracts | OS calls, compiler imports, UI widgets |
| `source/store` | Immutable text, overlays, source maps, identity | User-visible rendering, debug control |
| `source/providers` | Provider registry and normalized query interfaces | Unrestricted execution of source/configuration |
| `source/analysis` | Query planning, semantic graph queries, completeness | Separate copies of compiler semantics |
| `source/projection` | Fold selection, exact spans, compact text/structured renderers | Source writes |
| `source/session` | Agent preferences, help state, jump list, selected handles | Debug target state ownership |
| `source/transactions` | Versioned preview/apply/undo receipts | Hot patching without debug-service admission |
| `source/config_analysis` | Observations, owner-specific resolution, config use graph | Replacing all configuration owners |
| `source/change_analysis` | VCS queries, symbol/range mapping, impact | Claiming that a changed line caused a failure |
| `source/debug_bridge` | Source-to-frame mapping and read-only debug context | A second debugger service/evaluator |
| Protocol/UI adapters | MCP/LSP/DAP/Neovim/TUI translation | Independent business logic |

Package reusable parts as libraries; keep binaries as composition roots. Preserve the shared REPL/debugger library and standalone binary decision [C01]. A shared library loaded by two processes does not automatically share registries: remote clients need an explicit service host and authenticated protocol.

### 3.3 Dependency and admission rules

A lightweight outline open must not load the full compiler, all language servers, all debugger adapters, or GPU stacks. Provider modules load lazily. Bootstrap-only builds can offer a lexical/outline fallback with truthful capability metadata. A failure in one language-server process must not terminate unrelated views or debug sessions.

## 4. Language providers

### 4.1 Capability levels

| Level | Evidence available | Permitted claims |
|---|---|---|
| L0: raw text | File snapshot and line map | Exact text, substring search, explicit ranges |
| L1: syntax | Parser/Tree-sitter tree or labeled heuristic outline | Structural folds, syntax nodes, candidate occurrences; not resolved semantics |
| L2: semantic navigation | Compiler or admitted language server | Resolved definitions/references, types, offered code actions, capability-dependent call hierarchy |
| L3: program analysis | HIR/MIR or equivalent analysis adapter | Alias-aware effects, CFG, def-use, slices within stated scope |
| L4: runtime evidence | Debugger/trace backend and matching build | Observed frames/values/writes/events, bounded by capture coverage |

Tree-sitter supplies concrete syntax and incremental updates, not a universal type checker or whole-program effect engine [E-TS]. Different capabilities may have different levels for the same document. Never promote a syntactic assignment match to “all possible writers.”

### 4.2 Provider matrix

| Language | Structure provider | Semantic provider | Debug/config emphasis |
|---|---|---|---|
| Simple | Existing native lexer/parser/outline; shared immutable AST | Compiler query API, HIR/MIR, TLDR and expansion provenance | Ownership, borrow/effects, generics, macros/AOP, fibers, interpreter/native mapping |
| SDN | Native SDN lexer/parser with spans and lossless source slices | Schema + actual configuration-owner resolver | Key types, duplicates, constraints, source of effective values, consumers and override chain |
| SHS | Detected dialect's native shell parser or suitable Tree-sitter grammar | Shell-specific variable/command/environment analysis | Assignments, exports, cwd, pipeline/redirection flow, sourced-file dependencies, process exit provenance |
| C/C++ | Tree-sitter C/C++ | Optional clangd and compiler analysis adapter | Per-file compile commands, defines, includes, target/sysroot, pointer/FFI uncertainty |
| Rust | Tree-sitter Rust | Optional rust-analyzer; compiler effects only through a separate admitted provider | Features/target, macro expansions, ownership types, build-script trust |
| Python | Tree-sitter Python | Optional Pyright or another registered Python LSP | Interpreter/import environment, dynamic dispatch, monkey-patching uncertainty |
| Others | Registered grammar/query bundle | Optional registered LSP | Structural features first; no implied debugger or flow-analysis support |

clangd's parsing depends on compile commands, not merely file contents [E-CLANG]. Rust analysis can involve build scripts/proc macros; treat that as execution requiring workspace trust [E-RUST]. Python analysis depends on configured language version/import environment [E-PY]. These dependencies must appear in analysis provenance.

### 4.3 Provider registration

Use SDN manifests for language IDs, extensions, dialect/shebang rules, parser identity, query-set version, optional LSP launch specification, workspace-root rules, and capability declarations. JSON remains appropriate on MCP/LSP/DAP wires and in external tool formats that require it; SDN is the Simple-owned configuration format, not a reason to rewrite external standards.

Resolve conflicting registrations deterministically and explain the chosen provider. Never auto-download executable grammars or launch arbitrary workspace-defined binaries during a read. Native grammar plugins and external scanners are executable code; admit trusted versions and isolate where supported.

### 4.4 SDN-specific work

Preserve comments, ordering, source spelling, and source ranges alongside parsed values. Canonical encoding is useful for identity, not lossless viewing. Add document symbols for mappings, sections, tables, and lists; key hover from schema documentation; references to supported schema/include declarations; duplicate/unknown/deprecated-key diagnostics; and owner-approved migration fixes.

Do not invent SDN include/interpolation semantics. Expose only features supported by the actual owner/schema. When resolution depends on environment or evaluation, display raw, evaluated, effective, and runtime-consumed values separately. An observed/generated SDN report is not a policy file and must not override user choices merely because it exists.

### 4.5 SHS-specific work

A `.shs` file may be a POSIX-shell-compatible script, Bash, or a Simple/sosh dialect. Use explicit language metadata first, then configuration/shebang and parser evidence. Ambiguity returns a dialect-selection warning and a safe text/structural fallback; it does not run the script to determine its language.

Show command blocks, functions, conditionals, loops, pipelines, exports, assignments, and sourced-file groups. Analyze obvious reads/writes and known command effects conservatively. `eval`, computed command names, arbitrary external commands, and dynamic `source` paths are unknown-effect boundaries. A read-only source view must not execute substitutions, imports, scripts, or commands.

Recheck the namespace/type-collision issue documented in the inspected normalization adapter before importing native shell and compiler parsers into one process [R-DIALECT]. Fix namespace resolution or use a sanctioned provider-process boundary; do not fork the grammar to bypass it.

### 4.6 Cross-language navigation

Maintain language-qualified symbol identities and explicit FFI/import edges. A Simple call into C can resolve through generated binding metadata when available; otherwise show an unresolved external boundary. Selecting a Rust/C/Python frame uses its language provider, but source viewing support does not automatically provide runtime control for that language.

## 5. Snapshots, positions, and shared caches

### 5.1 Identity model

A source operation carries a `WorkspaceId`, logical agent session, and immutable `SnapshotId`. A snapshot identifies the worktree/SCV revision, overlay owner, document URI, content digest, language/dialect, parser version, and relevant semantic environment. Semantic results additionally identify dependency generations, target/features, compiler/provider versions, and any expansion generation. Runtime observations additionally carry `DebugSessionId`, target/process/fiber identity, build ID, code generation, and stop epoch.

A `SymbolId` is a semantic identity, not a line number or Tree-sitter node address. A `NodeRef` is valid within a stated snapshot; cross-edit remapping is best effort and must fail explicitly when ambiguous. A Tree-sitter node pointer is not a durable ID. Copy/update trees according to Tree-sitter's lifetime and concurrency contract [E-TS-EDIT].

### 5.2 Coordinate rules

Retain the original file bytes and declared/detected encoding. Internally use explicit byte ranges over a decoded UTF-8 source representation, plus a shared position map back to original bytes; do not silently rewrite non-UTF-8 files. A decoding failure returns an explicit binary/encoding limitation rather than lossy editable text. LSP conversion uses the negotiated encoding; Neovim adapters convert to its byte-oriented positions; human source line labels are one-based absolute positions. Never confuse display columns, Unicode scalar positions, UTF-16 code units, bytes, and screen cells. Test Korean text, combining marks, emoji, tabs, CRLF, and no-final-newline files.

Line numbers remain available in structured results even when not displayed. A selected view handle or symbol identifies a target without visible line numbers. Each rendered span maps back to the original source; virtual hints, metadata, folds, and wrapped lines map to annotations or synthetic nodes, never to editable source bytes.

### 5.3 Unsaved buffers and external changes

The editor buffer is authoritative for an editor-owned overlay. MCP reads must explicitly select that overlay or report that they read disk. A build based on disk must not be described as verifying unsaved editor content. Per-agent worktrees and overlays must not leak into other agents' snapshots.

Version-check changes, invalidate stale views, and publish change events. On source-file deletion, retain an immutable historical snapshot if authorized, mark it deleted, and refuse normal writes through that historical view. For generated/macro source, preserve both generated and origin locations.

### 5.4 Reuse the cache/SCV plan

Use the existing/planned shared AST → HIR → MIR → object cache interfaces, single-flight production, immutable results, and short-lived read handles. Avoid retaining entire compiler contexts per agent. Store optional annotations as sparse side data rather than expanding every AST node. Use dense attributes only for broadly needed properties.

Presentation settings (`num`, `info`, `hint`, fold state) must not invalidate parser/semantic caches. Semantic keys include relevant configuration and target identity; a host-independent syntax result must not accidentally become host-dependent merely because it is viewed in a container.

Where the `.rr` reverse-reference design is adopted, keep usage/reference-count churn in `.rr`, not declaration TLDR records. Publish through the common SOSIX atomic-write facility. Failed reverse-reference updates require the agreed full consistency recheck before dependent cached results are trusted [C01]. An ordinary UI read should not rewrite persistent `.rr` counts; record analysis dependencies in memory and publish durable dependency changes through the existing ownership rules.

Compact IDs are lookup accelerators, not proof of identity: verify collisions against the full content identity. Preserve the project's canonical-endian and hash-policy decisions. Do not replace security-sensitive evidence digests with a noncryptographic cache hash.

## 6. Agent-session preferences

### 6.1 Proposed state

```text
ViewSessionState
  workspace_id
  agent_session_id
  parent_agent_session_id?       # relationship, not shared preference ownership
  session_generation
  preferences_version
  line_numbers = false
  inline_info = important
  virtual_hints = false
  decoration_mode = ascii       # plain MCP default; UI can negotiate unicode
  help_seen_version = none
  current_view_id?
  selected_node_or_annotation?
  navigation_history
  fold_state_by_view
  recent_change_filter = last_7_days
  expiration / explicit resume policy
```

Choose the Unicode profile for a client that supports it; then use `▌`. Plain MCP text defaults to ASCII decorations unless the agent/client explicitly selects Unicode. Do not infer font rendering support solely from locale. `▌` is ordinary Unicode and does not require a Nerd Font; it is a Simple rendering convention, not a standard mandated by Neovim [E-NVIM].

“ASCII decorations” does not mean the underlying source is ASCII: preserve original Korean identifiers, strings, and comments. A strict ASCII transport needs a separately declared escaped representation with reversible mapping, not silent transliteration of source.

### 6.2 First-open and persistence rules

The first **successful** source view atomically includes a short Essential-help block and records its help version. A missing file or failed request does not consume first-open help. Concurrent first opens produce one help emission. Reconnecting a transport with the same authorized logical session preserves preferences; a new subagent starts independently with line numbers off and help unseen.

Preferences persist across files, navigation, searches, view refresh, and debugger entry for that logical agent. Source navigation changes no other agent's settings. Explicit session resume can restore state after server restart; otherwise return `session_expired` and create a fresh session rather than pretending state survived.

Do not infer subagent identity from tool prose, working directory alone, or the MCP connection. The agent manager supplies an authenticated logical-session binding. When a client cannot distinguish subagents, report the isolation limitation; do not claim independent first-open behavior.

### 6.3 Toggle safety

The visible command is `num`, not separate long on/off commands. Internally send `set line_numbers=true/false` with an expected preference version and request ID. A retried “toggle” must not flip twice. Apply the same rule to `info` and `hint`. Toggling numbers or hints changes presentation only; opening details is an action, not a permanent boolean preference.

### 6.4 SDN defaults versus session overrides

Proposed configuration example; the keys belong to a new schema and require parser/schema tests before deployment:

```sdn
source_view:
  schema: simple-source-view-v1
  line_numbers: false
  inline_info: important
  virtual_hints: false
  decoration_mode: ascii
  first_open_help: essential_once
  footer: compact
  default_open: outline
  navigation_open: focused
  fold_unrelated: true
  budget_tokens: 2000
  recent_changes:
    mode: last_touch
    since: 7d
```

This supplies defaults. A session `num` command overrides only that session; it does not rewrite this file or another agent's preferences. Explicitly saving a user default is a different action. Keep server-controlled authorization/resource ceilings outside client-overridable display preferences.

## 7. Source-view examples and folding

All examples are illustrative, not actual repository source or claims of implemented tools. Code rows preserve source text before the annotation boundary. Synthetic rows begin with the boundary. The Unicode examples use `▌`; ASCII rendering substitutes `|` **only in decoration fields**, not arbitrary source characters.

### 7.1 First file open without intent

```text
src/controller.spl  outline  view:v1  snapshot:s42
▌ Outline only. Open a symbol or supply intent.
▌ + imports (8)
enum ControllerState:                       ▌ + 3 variants
class Controller:                           ▌ + 4 methods
fn create_controller() -> Controller:        ▌ + body
▌ + tests (6)

▌ Essential: open <symbol> | /text | gd | back | detail <id>
▌ za: fold/expand selected node; outline: close all bodies
▌ [ess] [adv]
```

All bodies are closed. A folded class does not simultaneously pretend that its hidden methods are expanded. Request `outline depth=2` to reveal member signatures without revealing their bodies. The “Outline only” message is view guidance, not a compiler warning.

### 7.2 Second file open

```text
src/cache.spl  outline  view:v2  snapshot:s42
▌ + imports (5)
class Cache:                                ▌ + 7 methods
fn create_cache() -> Cache:                  ▌ + body
▌ + tests (9)

▌ [ess] [adv]
```

No automatic Essential-help block. No verbose setting status or repeated explanation. An explicit `ess` always shows help on demand.

### 7.3 Navigation to a method

```text
src/controller.spl  focused  view:v3  snapshot:s42
use .command.Command
▌ + other imports (7)
class Controller:                           ▌ - structure
    fn init():                              ▌ + body
    fn submit(cmd: Command):                ▌ + body
    fn process(cmd: Command):
        val state = self.state
        if state == READY:
            self.submit(cmd)
        else:
            return InvalidState
        sassert self.state == BUSY            ▌ E1
    fn reset():                             ▌ + body
▌ + other definitions/tests (7)

▌ E:1  hidden:0
▌ [ess] [adv]
```

The target method and necessary control context are visible; unrelated method bodies remain closed. The relevant import is actual source. Parent/class structure is opened only far enough to expose the target. Navigation does not require a visible line number.

### 7.4 Intent-based open

```text
source_open(path="src/controller.spl",
            intent="Find possible writes to Controller.state before this assertion",
            budget_tokens=2000)
```

The query planner resolves the target, identifies needed context, and returns writer sites, controlling conditions, relevant types/imports, and uncertainty boundaries. It must not promise exhaustive writers when only lexical matches or a partial index are available. Record why each span was selected, omitted ranges, unresolved boundaries, and an expansion handle.

### 7.5 Imports and non-block folding

Treat imports/includes/exports, declaration lists, top-level assignments, SDN scalar groups, and SHS exports as synthetic groups only when useful. Preserve original ordering and per-item ranges. Noncontiguous groups use a range set, never a fabricated contiguous range. Conditional imports and C preprocessor regions remain tied to their conditions. Never hide a Python import's possible side effects by labeling it harmless boilerplate.

Relevant imports are expanded individually while unrelated ones remain grouped. A cross-file resolution result must carry the import/re-export path where useful. Folding is presentation only; it does not reorder or remove statements from analysis.

### 7.6 Focus and reopen policy

An explicit new target opens only that target's dependency/context closure in the new view. Back/forward restores the previous view's fold state. A plain reopen restores the saved view unless `outline` is requested. `outline` closes all bodies, including synthetic groups. `raw` returns exact source without decorations and with explicit range/size bounds.

Large outlines paginate and retain parent context. A folded node can show aggregate diagnostics/changes after the boundary, so relevant errors are not invisible simply because their bodies are closed. No background claim of exhaustive “0 errors” is allowed when analysis has not run.

### 7.7 Selection before serialization

Adopt the useful Context Mode pattern: retain/index full evidence, return a bounded intent-relevant selection, and allow follow-up retrieval [E-CONTEXT]. For source, use syntax and semantics before text ranking. Search ranking alone is not a dependency proof. Do not summarize or rewrite code tokens inside a source segment; synthetic summaries are separately labeled.

An omission ledger lists source ranges, reason, selection coverage, and next retrieval handles. If the budget cannot include a necessary branch, alias boundary, or relevant definition, return a visible `partial_context` marker. Provide `exhaustive` analysis mode and paged `raw` viewing so correctness reviews are not trapped by the initial selection.

### 7.8 The same view across languages

These examples are illustrative source projections. Headers identify language/dialect and provider level; no Tree-sitter-only view claims inferred types or a complete call graph.

**SDN: navigate to a setting, with unrelated groups folded.**

```text
project.sdn  focused  language:sdn
build:                                      ▌ - mapping
  compiler: clang                           ▌ CFG K1
  target: x86_64-linux
container:                                  ▌ + mapping
▌ + other settings (6)
▌ [ess] [adv]
```

`detail K1` explains the raw setting, effective value, winning source, actual consumer, and run/build evidence. No compiler or container is launched to render this view.

**SHS: structure without executing the script.**

```text
build.shs  outline  dialect:bash  provider:syntax
#!/usr/bin/env bash
▌ + imports/source commands (2)
export CC=clang                              ▌ assignment/export
build() {                                   ▌ + body
check() {                                   ▌ + body
▌ + top-level commands (3)
▌ [ess] [adv]
```

A computed `source` path or `eval` remains an unknown effect; expanding it shows source, not execution results.

**C, Rust, and Python: the same outline contract.**

```text
controller.c  outline  provider:tree-sitter/c
▌ + includes (4)
struct Controller {                         ▌ + members
int submit(struct Controller *c) {          ▌ + body
▌ [ess] [adv]
```

```text
controller.rs  outline  provider:tree-sitter/rust
▌ + use declarations (3)
struct Controller {                         ▌ + fields
impl Controller {                           ▌ + methods
▌ [ess] [adv]
```

```text
controller.py  outline  provider:tree-sitter/python
▌ + imports (4)
class Controller:                           ▌ + members
async def run_controller():                  ▌ + body
▌ [ess] [adv]
```

Definition/type requests can start an admitted semantic provider when requested. Otherwise they return the available syntactic candidates or an explicit unsupported result. Native braces, indentation, decorators, and conditional compilation stay attached to their actual source ranges; the renderer does not translate these languages into Simple syntax.

## 8. Compact help and navigation

### 8.1 Default footer

```text
[ess] [adv]
```

Within a rendered code view, prefix the footer with `▌` or ASCII `|` as a synthetic row. These are textual affordances, not guaranteed clickable MCP buttons. A Neovim/TUI/plugin may map them to actions; an LLM calls the corresponding typed tool. Do not present a text transcript as an interactive application.

### 8.2 Essential help

Keep the first-open help to two or three compact lines. It covers opening a symbol, searching, definition navigation, back, folding, and details. `gd`, `za`, and `/` are familiar Vim-style conventions; Simple-specific bindings are only installed by the bridge and must not override user mappings without consent.

### 8.3 Advanced help

```text
Display: num | info | hint | outline | raw
Analyze: callers | callees | refs | writes | type | flow | cfg | slice
Debug:   stack | locals | watch | frame | repl | capabilities
History: changes | diff | impact
Config:  env | config | explain
Fix:     actions | preview | apply
```

Show only available categories or explicitly label unsupported operations with reasons. Do not include this table in every source response. `num`, `info`, and `hint` settings persist per agent/subagent; `raw` is a requested view mode, not a hidden change to source-writing behavior.

Navigation actions accept stable view handles, symbol IDs, diagnostic IDs, or source positions. Avoid requiring the agent to scroll one line at a time. Human `j/k` movement stays local to the frontend; MCP should support semantic jumps and bounded ranges.

## 9. Annotations, hints, and detail expansion

### 9.1 Boundary rule

```text
val state = self.state                      ▌ W1 fix:1
self.state = BUSY                           ▌ ~7d C1
sassert self.state == BUSY                   ▌ E1
```

Every generated end-of-line annotation starts after the rectangular boundary. Add it after the **complete** source line, never inside a string or at a fixed column that cuts the line. If the line is too long, put metadata on a following synthetic line. No color is required to interpret the output.

ASCII equivalent:

```text
val state = self.state                      | W1 fix:1
self.state = BUSY                           | ~7d C1
sassert self.state == BUSY                   | E1
```

Source itself may contain `|`, `▌`, or `/* ... */`. The structured segment map is authoritative; neither the client nor an edit tool may recover source by splitting on a delimiter or deleting comment-looking text.

### 9.2 Annotation catalog

| Category | Compact example | Default visibility | Detail contents |
|---|---|---|---|
| Compile/lint error | `E1 fix:1` | Important | Stable diagnostic code, spans, related locations, candidate fixes, analysis revision |
| Warning | `W1` | Important | Explanation, rule, severity source, confidence, suppression policy |
| Assertion/exception | `ASSERT A1` | Relevant debug stop | Evaluated operands, stop epoch, stack, capture limitations |
| Recent committed change | `~7d C1` | Relevant changed lines | Resolved time window, commit, diff, date basis, line-mapping confidence |
| Uncommitted change | `MOD M1` | Changed lines | Index/worktree/overlay layer and exact diff |
| Breakpoint/current frame | `BP B1`, `STOP` | Debug view | Verified/pending state, condition, target, hit count, stop identity |
| Type | `T1` | On request | Declared/inferred/concrete type, alias chain, ownership/effects, provider |
| Parameters/return | `H1` or virtual hint | `hint` opt-in | Parameter/type resolution and source location |
| Static writers | `WR Q1` | Writer intent | Must/may writes, alias paths, unknown external effects, coverage |
| Runtime value/write | `V1`, `WRITE O1` | Debug intent | Value/old value if captured, writer PC/source, process/fiber, trace coverage |
| Calls/references | `CALL Q2` | On request | Incoming/outgoing edges, dispatch uncertainty, pagination |
| Control/data flow | `CF Q3`, `DF Q4` | On request | Blocks, conditions, definitions/uses, dependence edges |
| Config dependency | `CFG K1` | Relevant intent | Winning value/source, overrides, consumers, runtime observation |
| Test/coverage | `TEST T2` | On request | Test identities, execution/build ID, coverage freshness; not implied correctness |
| Macro/generic/aspect | `GEN G1` | Relevant intent | Expansion origin, instantiation, advice/pointcut identity, code generation |
| Analysis limitations | `PARTIAL`, `STALE` | Always when applicable | Missing provider/dependencies, expired snapshot, unrecorded state |

`E1`, `W1`, `C1` are compact **view-local handles**, not diagnostic rule codes or counts. Counts use footer forms such as `E:2 W:1`. IDs remain bound to a view/snapshot; an old `E1` cannot silently resolve to a new diagnostic after refresh.

### 9.3 Type and parameter hints inside code

Optional projected view:

```text
src/controller.spl  focused                  ▌ virtual hints enabled
val state /*: ControllerState */ = self.state
queue.push(/*item:*/ cmd)
```

The hints are virtual decorations. In Neovim, render them through inlay hints/extmarks, not buffer edits [E-NVIM]. For plain MCP text, mark the view as decorated and preserve a raw-source handle. C-style comments are only a visual convention: Python, SDN, and some SHS/Simple dialects do not accept that syntax as comments. Default hints off, especially for raw code-generation/editing workflows. Never strip all real comments to reconstruct source.

### 9.4 Details

```text
self.state = BUSY                           ▌ ~7d C1  WR Q1
                                           ▌ C1: committed change; diff available
                                           ▌ Q1: 3 candidate writers; alias coverage partial
                                           ▌     submit(), reset(), on_failure()
```

`detail C1` retrieves the revision-pinned diff/provenance. `detail Q1` retrieves the analysis result and its completeness. `detail E1` shows the message and available fixes. Large details become a separate paginated panel/resource rather than expanding every source line.

### 9.5 Independent toggles and footer

`info` hides/shows end-of-line facts; `hint` controls in-code virtual hints; `num` controls line labels. Hiding inline information does not erase diagnostics, alter compilation, or silently suppress error counts. The footer can retain `E:1 W:2 hidden:3` when appropriate. Report `analysis:not-run` or `partial` rather than inferred zeroes. Optional expanded status can show snapshot, selected provider, budget, and current preferences; keep that off by default.

### 9.6 Line numbers when enabled

```text
125:     sassert self.state == BUSY           ▌ E1
```

Use a distinct numeric gutter such as `125:` so ASCII `|` metadata is not visually confused with another separator. Numbers are absolute original lines, not renumbered projection rows. Hidden code and virtual lines do not advance source line numbers. No claim is made that numbering universally improves LLM reasoning; benchmark it as an interface choice (§21).

## 10. Diagnostics and safe automatic fixes

### 10.1 One canonical diagnostic path

Extend the inspected `DiagnosticV1` model [R-DIAG] with additive identity/provenance wrappers as needed: snapshot, producer/version, analysis run ID, document version, target/configuration identity, and links to candidate actions. Preserve code, message, severity, all source labels, nested diagnostics, macro trace, replacement spans, and confidence.

Use this path:

```text
compiler / schema validator / script analyzer / external LSP
    -> normalized diagnostic + provider provenance
    -> shared diagnostic store keyed by snapshot
    -> CLI / MCP view / LSP diagnostics / debugging screen
    -> candidate action -> preview -> versioned edit -> reanalysis
```

Do not treat a nonzero process exit as an ordinary compiler diagnostic without checking whether the producer failed to launch, timed out, crashed, or emitted malformed output. A zero exit does not imply no warnings. An empty result is valid only for a completed admitted analysis with no findings.

### 10.2 Compact display and detail

```text
val unused_state = self.state               ▌ W1 fix:1
val result = missing_name                   ▌ E1

▌ E:1 W:1 actions:1
▌ [ess] [adv]
```

`fix:1` means an available candidate, not a validated repair or automatic application. The example does not assert that replacing `missing_name` is safe; a spelling candidate can refer to the wrong object.

Expanded detail:

```text
W1  unused-binding                         ▌ producer:Simple  snapshot:s42
Candidate F1: remove unused binding
Confidence: safe                           ▌ eligibility depends on effect checks
Validation: proposed; not applied
Preview: exact source edit / diff
```

An unused binding can have an effectful initializer. Removing it is eligible for unattended fixing only when the producer's semantics justify that transformation; otherwise preserve evaluation or require review.

### 10.3 Fix classification

| Field | Meaning |
|---|---|
| `confidence` | Preserve existing `safe`, `likely`, `uncertain` producer classification. |
| `applicability` | Applicable, stale, blocked by missing capability, conflicting, or requires choice. |
| `validation` | Proposed, schema/range-checked, statically checked, compiled, targeted-tests-passed, full-required-tests-passed. |
| `effects` | Source files touched; import/config/build/run effects; whether execution is required. |
| `authorization` | Preview-only, explicit user/agent apply allowed, or admitted batch-safe policy. |

LSP `isPreferred` is ranking, not proof of safety. A server-supplied command can execute code and must go through policy. `source.fixAll` must be confined to clear fixes not requiring a choice; do not silence errors or synthesize speculative classes/types under “safe fix all” [E-LSP-ACTIONS].

### 10.4 Apply transaction

1. Resolve the action against the diagnostic's source snapshot and provider generation.
2. Fetch/validate the complete edit set, including deletions (`newText: ""`), multiple edits, files, and resource operations.
3. Verify all original document versions/content identities and authorization; reject overlapping incompatible edits.
4. Show the exact preview. Apply to the editor-owned overlay through the editor, or to a controlled workspace transaction for disk-owned files.
5. Reparse/reanalyze affected dependencies. Run required build/tests under separately authorized execution policy.
6. Return a receipt distinguishing **edit applied**, **original diagnostic resolved**, **new diagnostics introduced**, and **verification completed**.

LSP clients differ in workspace-edit atomicity support. Negotiate their failure-handling capabilities; do not promise cross-file atomicity the editor cannot supply. For disk edits, stage and journal a multi-file transaction: individual atomic file renames alone are not an atomic multi-file commit. On partial failure, report exact state and controlled recovery; never overwrite concurrent user work with a blind rollback.

### 10.5 Concrete hardening in existing handlers

Replace handwritten JSON scanning with the shared strict parser and typed conversion. Preserve all original file URIs and every replacement. Do not replace every action URI with the request file's URI. Use actual editor versions when known; for disk-only edits require content preconditions. Correct the empty-replacement check. Test nested JSON, escaped strings, Windows/UNC paths, multiple edits, deletion-only fixes, generated-file restrictions, and source mappings.

Keep older tool names through compatibility façades. Add action discovery/preview/apply to LSP-MCP through the same service; do not build a second fixer inside the bridge.

### 10.6 Diagnostics versus runtime failures

A compile error, a warning, a test assertion, a runtime exception, and a fatal crash are distinct event kinds. They may share source annotations but must retain separate provenance and severity semantics. A compile failure can open a focused source view without inventing a runtime stack. An assertion can provide runtime values only when captured from the target or bundle.

## 11. Source analysis for debugging

### 11.1 Shared query contract

Every result includes the operation, snapshot, selected scope, provider/capabilities, completeness, unresolved boundaries, evidence spans, cost/budget status, and continuation token when truncated. Distinguish `exact_within_scope`, `conservative_may`, `heuristic`, `runtime_observed`, and `unknown`; avoid unsupported numeric confidence scores.

An empty result means a completed query found no results within its declared scope. `unsupported`, `unavailable`, `timeout`, `cancelled`, `stale_snapshot`, and `partial_index` are separate outcomes. Existing LSP empty-success handlers must not be reused as semantic evidence [R-LSPHAND].

### 11.2 Calls and references

Implement incoming/outgoing call edges from resolved symbols, including calls through methods, closures, generic instantiations, dispatch, callbacks, FFI, macros, and AOP advice when available. Return callsite ranges, dispatch kind, target candidates, and unknown edges. Direct and transitive queries have separate depth/edge budgets and cycle handling.

References are classified as declaration, read, write, read/write, borrow, address-taken, call, import, type use, or unresolved occurrence. A references list is not automatically a call graph. An unused/unreachable candidate is not necessarily safe to remove.

### 11.3 Types

Return declared, inferred, and instantiated types; type aliases; generic substitutions/constraints; ownership/borrow/mutability; nullability or union alternatives; effects; layout/ABI where requested and available; and type origin. Separate static type from observed runtime type and optimized-out data. Provide hover-sized summaries and lazy expanded type trees with recursion/cycle limits.

### 11.4 Writers and state changes

Static writer analysis covers assignment, compound update, indexed/field mutation, mutable borrows, aliasing, ownership transfer, captured references, method effects, globals, callbacks, atomics, and known foreign functions. Classify must-write, may-write, and unknown external effects. Field-sensitive analysis is preferred where available; label coarse whole-object results honestly.

Start with precise intraprocedural analysis, then add interprocedural summaries and configurable context sensitivity. At unresolved FFI or dynamic dispatch, keep an explicit unknown-effect edge; do not hide it because intent ranking finds it inconvenient.

Runtime writer capture requires a real admitted data watchpoint or instrumentation backend. Negotiate DAP data-breakpoint support where that adapter is used [E-DAP]. An MCP `set_variable` event is not evidence that arbitrary program writes are observed. Record source/PC, call stack if available, object/address identity and lifetime generation, byte range, target/process/thread/fiber, stop/event sequence, and old/new values **only when actually captured**.

Hardware watchpoints may be limited by size, alignment, slots, target support, and debugger semantics. A stopped watchpoint may not provide a trustworthy old value. Software tracing changes timing and can drop events. Return those limitations and the observation start/end window. “Last observed write” is not “last write ever.”

### 11.5 Control and data flow

Build CFGs from admitted compiler IR with source maps. Include exceptional edges, cleanup/defer paths, loops, early exits, async suspension/resumption, and generated control flow where applicable. Data flow includes definitions/uses, reaching definitions, effects, aliases, and value transformations.

Backward slicing from an assertion/expression includes both data and control dependence. Forward slicing supports change impact and affected-value analysis. A static path is a possibility; an observed path requires execution evidence. Path feasibility beyond supported analysis is `unknown`, not a guessed proof.

### 11.6 Async/concurrency

Associate tasks/fibers with spawn/await relationships, synchronization events, shared-state accesses, locks, atomics, and ring enqueue/dequeue provenance where instrumented. Keep physical stack, logical async stack, and happens-before information separate. A static potential race is not a confirmed observed race; an event timeline without sufficient synchronization capture is not a complete execution order.

### 11.7 Macro, generic, and aspect provenance

Map expanded statements to original source, macro definition/invocation, concrete generic instance, advice generation, pointcut identity, and affected directory TLDR state. A view can switch between source and expansion without losing its selected origin. Mark unmapped generated instructions explicitly.

Use planned dependency invalidation rules rather than inventing a second expansion cache. Interface-changing macro/AOP edits and generic specialization changes affect semantic snapshots; purely visual fold changes do not. Track runtime code generations for replacements so a frame executing old code is not displayed as though it executes a newly edited body.

### 11.8 Combined debugging query

A proposed `source_debug_context` operation composes existing lower-level queries, not a separate reasoning engine:

```json
{
  "agent_session_id": "agent-a",
  "debug_session_id": "debug-7",
  "stop_epoch": 12,
  "focus": {"assertion_id": "assert-3"},
  "include": ["stack", "writers", "backward_slice", "changes", "config"],
  "budget": {"tokens": 2000, "graph_edges": 300}
}
```

Return selected source/evidence, explicit possible versus observed causes, missing capabilities, and follow-up handles. Do not label a recent commit as the root cause solely because it touches the slice.

## 12. Debugging screen and shared REPL integration

### 12.1 One target authority

Extend the existing `DebugServiceV1`, `DebugWireV1`, capability/policy/receipt and evidence contracts [R-DBGSVC], [R-DBGARCH], [C01]. The source service supplies code and analysis; the shared debugger library owns target access and command semantics. Human REPL, screen, MCP, DAP, and test runner are clients. Do not introduce separate breakpoint registries, evaluators, or session owners per frontend.

Mutating operations require a control lease or equivalent serialized authority. Multiple viewers may inspect one stopped target, but two clients must not race `continue`, `step`, `set_variable`, or replacement. Inspection consistency is pinned to a stop epoch; continuing invalidates variable/frame handles from the previous epoch.

### 12.2 Proposed debugging screen

```text
Session debug-7 | interpreter | stopped:assert | build:b42 | epoch:12
+------------------------+----------------------------------------------+
| Stack / fibers         | Source: controller.spl                       |
| > process()            | fn process(cmd: Command):                    |
|   run_test()           |     sassert self.state == BUSY   | ASSERT A1 |
| fiber:worker-3         |                                              |
+------------------------+----------------------------------------------+
| Locals / watches       | Details / changes / configuration            |
| self.state = READY     | A1: expected BUSY; captured READY            |
| cmd = <expand>         | C1: relevant recent change; diff available   |
+------------------------+----------------------------------------------+
| REPL: selected frame=process, effect policy=inspect                    |
| > type self.state                                                      |
+------------------------------------------------------------------------+
[ess] [adv]
```

This is a layout proposal, not a claim that a particular current Simple screen implements it. Provide a narrow-terminal layout with one selected panel; use the same view model for GUI/TUI/Neovim and MCP text. The event timeline and environment/config panel are on demand. Do not fill all panes eagerly with expensive data.

Selecting a stack frame opens matching source and focuses the active statement. Selecting a writer, diagnostic, config source, or diff navigates using the same jump list. Changing files does not change the debug target. A selected frame from an older code generation remains bound to that generation.

### 12.3 Assertion and test-runner flow

Preserve the earlier debugger delivery sequence [C01]:

```text
assert/test failure before destructive unwind
  -> capture failure identity and already-evaluated operands
  -> preserve real worker/process/fiber frame
  -> runner supervisor establishes authenticated DebugWireV1 route
  -> DebugServiceV1 creates/adopts target session
  -> shared REPL + source view opens the failing location
  -> inspect / capture / explicitly mutate or resume under policy
  -> original failed attempt remains failed
```

Never debug only the runner's wrapper stack. Avoid re-evaluating assertion operands with side effects. Define whether only one fiber, one process, or the entire target group is paused; expose that scope because other writers may continue running. Give CI a bounded noninteractive policy so an assertion does not hang indefinitely waiting for a human.

### 12.4 Stack trace policy

Interpreter assertions use logical frames; native assertions use admitted unwind/symbolization support. Include build/source identity and explicit missing/optimized-out/inline-frame information. Async/fiber traces include logical parent relationships when recorded, clearly distinguished from physical frames.

Fatal crashes use a minimal crash-safe capture path. Avoid heap-heavy formatting, compiler loading, networking, locks of uncertain state, or interactive REPL startup inside a corrupted process/signal handler. An external helper or subsequent process can symbolize and open captured evidence. Stack capture is best effort with truthful failure status, not an unconditional guarantee.

### 12.5 REPL operations

Inspection and evaluation are distinct. Reading stored locals is preferable to invoking arbitrary methods, getters, `repr`, overloaded operators, or constructors. An expression evaluator must classify/deny effects according to policy; “evaluate” is not automatically read-only. Session source definitions, scratch expressions, and edits carry their own overlay/generation.

The REPL can request source, types, writers, flow, environment/config explanations, diagnostics, and fixes through the shared query service. It does not need to call the MCP protocol internally. MCP and REPL translate to the same typed operations.

### 12.6 Dumps, server diagnosis, and hot replacement

A dump opens as a read-only post-mortem session with capture capabilities. Re-execution, checkpoint restoration, and deterministic replay are separate operations with separate evidence. Bundle manifests retain source/build/configuration identities, code generation, source maps, traces, and capture limitations. Source mismatch is a warning/refusal for exact mapping, not silent substitution of current checkout text.

Per-application SDF assertion/upload policy remains owned by the shared config infrastructure; SDN observations can report its effective resolution. Do not rename or replace the application policy format without an explicit compatibility migration.

Interpreter replacement precedes native replacement. Compatible function/method changes may publish a new generation; class layout/signature/closure/async-frame changes need versioning, migration, or restart. Existing frames/objects keep their admitted generation. Lower optimization alone does not make a binary reloadable. Replacement remains a distinct authorized debug transaction; a source edit or “fix applied” does not imply the running process changed.

Preserve original evidence and rerun regression tests from a clean build. A debugger-mutated session must not turn the original failing attempt into a passing verification result.

## 13. Environment and configuration analysis

### 13.1 Four contexts, not one ambient environment

Separate **host observations**, **analysis-tool environment**, **build effective configuration**, and **actual execution environment**. A cross-compiler host, target OS, container, remote worker, and LSP host can all differ. “Clang is installed” does not establish “this build used Clang.”

Reuse host configuration and build-environment identity infrastructure [R-HOST], [R-ENV]. Add inventory and explainability rather than a separate conflicting resolver. Keep `simple env` virtual-environment responsibilities distinct from a proposed broader doctor/config interface.

### 13.2 Proposed SDN artifacts

| Artifact | Purpose | Ownership |
|---|---|---|
| Existing `host.sdn` | User-selected host policy | User/config owner; do not overwrite during observation |
| `host_observed.sdn` | OS, CPU, tool availability and probe results | Generated, timestamped, read-only observation |
| `analysis_environment.sdn` | Provider binaries/configuration, language server inputs | Analysis session |
| `effective_config.sdn` | Resolved settings and provenance chain | Configuration resolver |
| `build_environment.sdn` | Exact tools/arguments/target/environment for a build | Build runner |
| `execution_environment.sdn` | Process/container/runtime observations | Runner/debug capture |
| `environment_diff.sdn` | Redacted comparison between runs/builds | Derived analysis |

These generated names are proposals, not verified current files. Store them in a configured local/session/build evidence directory, not automatically in tracked source. Use schema versions, capture time, scope, producer, freshness, and integrity identity. Immutable failure snapshots remain immutable; a refresh creates a new observation.

### 13.3 Inventory content

Record Rust (`rustc`, Cargo, rustup), C/C++ compilers (Clang/GCC/MSVC), linker, CMake/Ninja/Make/MSBuild, SDK/sysroot, debugger adapters, Simple compiler/bootstrap phase, Git/JJ/SCV, registered language servers, relevant GPU tools, and container backend **when needed by the selected project/target**. Avoid probing every installed tool on each read.

For each tool record executable resolution/path, version, target capabilities where discoverable, selected invocation/flags, selection source, availability status, trust/probe status, and checked time. Distinguish installed, selected, executable, compatible, missing, denied, timed out, and unknown. Resolve within the correct container/remote process environment, not just the MCP server's PATH.

Probe read-only files first. Executing `--version` still executes a binary: require trust, allowlisted argv, bounded process resources, and no shell evaluation. Do not download dependencies, source shell startup files, or run project build scripts during passive discovery.

### 13.4 Configuration provenance

For a setting such as `settings.os`, build compiler, linker flavor, or container isolation, expose:

```text
key: build.compiler
raw value: clang
resolved value: /opt/toolchain/bin/clang
winner: project configuration, source span S1
overrides: host default -> user override -> project value
consumer-specific override: absent
actual build invocation: recorded in build b42
analysis provider invocation: recorded in analysis a9
comparison: matched / mismatched / unknown
```

Use the configuration owner's actual precedence; host configuration already documents exceptions for consumer-specific variables [R-HOST]. Record evaluation dependencies and rejected/ignored values. Distinguish declared, effective, and observed values; a container request for an isolation mode is not proof it was actually established.

Add a config-use graph: key definition → override/evaluation → consumer source/build step → run/artifact. Dynamic lookups that cannot be resolved remain unknown. Query “who reads this setting?” separately from “what value won?” and “what did this run consume?”

### 13.5 Container and OS context

Report backend, requested/effective isolation, host/target OS and ABI, image/rootfs identity where relevant, source path mapping, mounts and permissions, cwd, user identity, resource limits, environment inheritance, network policy, and debugger permission restrictions. Some backends have no image or VM: mark not applicable rather than inventing container concepts.

Source URI mapping must resolve remote/container paths to the right local snapshot. Host inspection and container inspection are distinct scopes and permissions. A permission denial is an actionable result, not an empty environment.

### 13.6 Redaction and freshness

Never place raw tokens, credentials, private keys, full secret-valued environment variables, or sensitive dump payloads in default MCP output or source annotations. Store allowlisted data and redacted provenance. A hash of a low-entropy secret can still disclose it; use an approved keyed comparison mechanism where equality is needed, and restrict access to full internal fingerprints.

Record freshness per probe. A newly selected compiler, PATH change, SDK update, container change, or language-server configuration change invalidates relevant analysis caches. Do not rebuild everything when a purely presentational logging preference changes.

### 13.7 Example observed SDN record

The following is an illustrative output shape, **not an observation of the user's workstation**. A compiler version is deliberately omitted until actually probed.

```sdn
host_observed:
  schema: simple-host-observed-v1
  observation_id: example-observation-1
  scope: analysis_host
  completeness: partial
  tools:
    clang:
      status: selected_unprobed
      selected_by: project_config
      version_status: unknown
  configuration:
    build_compiler:
      key: build.compiler
      raw_value: clang
      source_file: project.sdn
      source_span_ref: example-span-1
      effective_path_status: unresolved
```

A real emitted record also carries capture time, producer identity, freshness, permitted paths, and source/build/run references. Use absence/status fields for unknown facts; do not emit invented versions or placeholder executable paths as measured values. Generate separate records for host, analysis container, build worker, and execution target when they differ.

## 14. Recent changes and regression analysis

### 14.1 Query semantics

| Mode | Meaning |
|---|---|
| `last_touch` | Current ranges whose selected-history last modification falls within the window |
| `touches_in_window` | Any matching commits affecting a symbol/range during the window |
| `net_diff` | Content difference between exact resolved base/head snapshots |
| `worktree` | Index, worktree, and editor-overlay differences, labeled separately |
| `impact` | Derived affected symbols/callers/config consumers/tests with uncertainty |

The default `~7d` tag uses a documented, frozen history predicate, not a shifting guess. Resolve relative time at query creation into absolute timestamps, timezone, date basis (committer date by default unless configured), and head revision. Reopening a frozen view does not silently move the window. A refresh makes a new query identity.

Git log filtering and tree comparison are distinct operations [E-GITLOG], [E-GITDIFF]. A tag names a revision, not necessarily “all changes since its date.” Resolve tag/branch refs once to exact commits and report the comparison semantics. Do not confuse commit author, committer, and actual runtime writer.

### 14.2 Mapping and presentation

Show `~7d C1` for a committed history match; `MOD M1` for uncommitted changes. A deleted line has no current line to annotate: place its detail at an enclosing symbol/fold summary or a deletion/tombstone entry. Account for renames, moves, merge commits, generated files, shallow history, and unavailable revisions. Heuristic symbol matching across revisions is labeled as such.

`detail C1` exposes commit metadata, source diff, symbol mapping, and base/head identities. `impact C1` traverses call/effect/config/test dependencies and reports incomplete edges. Do not automatically expose author email in a compact code view; use privacy-aware attribution on demand.

### 14.3 Passing-versus-failing comparison

Compare code, dependency lock state, compiler/toolchain, target flags, config resolution, environment, container/rootfs, and runtime inputs. Rank candidate differences as hypotheses linked to evidence. Preserve a distinction between correlation and demonstrated regression. A confirming test or controlled rerun can strengthen a hypothesis; recent code alone cannot establish causation.

## 15. MCP, LSP-MCP, LSP, and Neovim contracts

### 15.1 Small public tool families, shared typed operations

Retain existing entry points and names where clients depend on them. Internally route them to the same typed services. Do not implement one set of source semantics in `simple-mcp` and another in `simple-lsp-mcp`.

| Proposed tool family | Representative operations | Authority / behavior |
|---|---|---|
| `source_session` | open, resume, preferences, capabilities, close | Application-level view state; no implicit target control |
| `source_open` | outline, focused, raw, exhaustive selection | Snapshot-backed source projection with a bounded result |
| `source_navigate` | definition, symbol, search, fold, back, next page | Changes the requesting agent's view only |
| `source_detail` | annotation, diagnostic, type, history, omitted region | Fetches evidence referenced by a view-local handle |
| `source_analyze` | callers, callees, references, writes, flow, CFG, slice, impact | Explicit analysis kind and scope; no arbitrary shell command |
| `source_actions` | list, resolve, preview | Read-only fix/refactoring discovery |
| `source_edit` | validate, apply, undo transaction where supported | Authorized source mutation, separate from read-only tools |
| `environment_inspect` | observed, effective, actual, explain, diff | Scope-bound redacted environment/configuration inspection |
| Existing debug tools | stack, locals, frame, breakpoint, watch, evaluate, control | Adapters to the common `DebugServiceV1` command contracts |
| `source_debug_context` | combine stop, source, diagnostics, writers, changes, config | Evidence composition; does not silently resume or mutate |

These are logical families, not a requirement to expose a giant polymorphic tool. Split read-only and mutating operations so permissions, descriptions, and tool annotations remain accurate. Prefer a few well-described tools with typed query enums over hundreds of near-duplicate tools or a single unrestricted `execute` endpoint.

### 15.2 Example request and result

The following is an illustrative MCP `tools/call` request. It is not a claim that this tool is registered today.

```json
{
  "jsonrpc": "2.0",
  "id": 18,
  "method": "tools/call",
  "params": {
    "name": "source_open",
    "arguments": {
      "agent_session_id": "agent-a1",
      "workspace_id": "workspace-7",
      "path": "src/controller.spl",
      "target": {"symbol": "Controller.process"},
      "intent": "Inspect the assertion and possible writes to state",
      "budget_tokens": 2000
    }
  }
}
```

A service result should include the following information, carried in the appropriate MCP result fields:

```json
{
  "schema_version": 1,
  "view_id": "view-18",
  "snapshot_id": "snapshot-42",
  "agent_session_id": "agent-a1",
  "status": "ok",
  "completeness": "partial",
  "provider": {"id": "simple-native", "level": "semantic"},
  "presentation": {
    "line_numbers": false,
    "symbols": "ascii",
    "inline_hints": false
  },
  "projection_text": "src/controller.spl\n...bounded selected source...\n| [ess] [adv]",
  "source_map_ref": "view-18/source-map",
  "omission_ledger_ref": "view-18/omissions",
  "annotation_refs": ["view-18/E1", "view-18/W1"],
  "raw_source_ref": "snapshot-42/src/controller.spl",
  "limitations": ["Interprocedural writer analysis is not available for this provider"],
  "continuation": null
}
```

The ellipsis here stands for example payload content, not an instruction to hide omissions without tracking them. Production results must supply real omission entries and expansion handles. References in this example are opaque application handles; define their resolution contract rather than pretending they are automatically valid filesystem paths or standard MCP resource URIs.

MCP supports schemas and structured results [E-MCP]. Budget the **entire model-visible response**, including text and JSON, because structured data is not inherently hidden from the model. Follow the negotiated protocol's compatibility guidance; do not return an entire raw file in structured content and call a two-line text summary “context efficient.” Keep large raw evidence behind bounded resource/tool reads. A human editor may use a separate authenticated bulk-fetch route.

### 15.3 Result states and capabilities

Separate operational status (`ok`, `unsupported`, `denied`, `stale`, `error`, `cancelled`) from completeness (`complete`, `partial`, `not_evaluated`) and evidence kind (`syntax_candidate`, `resolved_static`, `observed_runtime`). Include reasons and next actions without turning failures into successful empty arrays.

Capability reports identify language, provider/version, target/configuration, operation, policy, and verification evidence. An operation may be available for a stopped interpreter but unavailable for a native dump. Tool discovery and capability negotiation must not fabricate runtime readiness.

Keep application session persistence independent of transport/session conventions. Negotiate supported MCP protocol versions explicitly; the inspected LSP-MCP code declares `2025-06-18` [R-LMCP]. This plan does not assume that hard-coding that version is appropriate forever, nor that changing protocol version supplies agent/subagent identity automatically.

### 15.4 LSP mapping and parity

Use standard LSP methods where they express the requested behavior [E-LSP]. Advanced data-flow, environment, and projection operations remain explicitly named extensions or MCP operations; do not mislabel custom methods as standard LSP.

| Shared service operation | LSP integration | MCP/view integration |
|---|---|---|
| Document/overlay store | `didOpen`, `didChange`, `didClose`, `didSave` | Snapshot-bound reads and editor-bridge overlays |
| Definition/type/implementation | Standard navigation requests | Direct semantic navigation |
| References and occurrences | References; document highlights | Read/write classification when provider supports it |
| Symbols and outlines | Document/workspace symbols | Bounded all-bodies-folded outline |
| Folding | Folding ranges | Structural and synthetic groups with range sets |
| Call graph | Prepare/incoming/outgoing call hierarchy | Depth-bounded callers/callees and uncertainty |
| Types and parameters | Hover, signature help, inlay hints | Detail and optional virtual hints |
| Diagnostics | Publish/pull diagnostics as negotiated | Shared diagnostics with view-local IDs |
| Fixes/refactoring | Code actions, resolution, versioned workspace edits | List, preview, explicit apply transaction |
| Semantic coloring | Semantic tokens as negotiated | Optional client rendering; no dependency on color |
| Rename/formatting | Standard requests when genuinely implemented | Shared version-checked edit preview/application |
| Debug state | DAP or bridge, not LSP alone | Shared debug context and source annotations |

Core usability work also covers completion resolution, declaration/type navigation, selection ranges, workspace symbols, formatting/range formatting, rename preparation, file-operation notifications, multi-root workspaces, document links, and CodeLens **where a provider has meaningful support**. Audit each before advertising it. None is permission to implement placeholder success responses.

Use a real JSON codec rather than ad hoc substring extraction for nested objects, escaped paths, multiline edits, and deletion text. Preserve document versions, diagnostic association, action data, related locations, all replacements, and disabled-action reasons. Handle protocol cancellation, bounded progress, initialization/shutdown, framing limits, and failures explicitly. Protocol stdout must contain only protocol messages; diagnostics/logging go through the designated channels or stderr.

### 15.5 External language-server broker

For C/C++, Rust, and Python, start or reuse a configured trusted language server only when semantic work is requested. Attach the correct workspace, compile commands/features/interpreter, and unsaved document overlays. Pin a result to the document version and provider generation that produced it. Do not claim freshness based only on arrival order.

Avoid broker loops: Simple's external-provider registry must not route a request back into the same Simple LSP-MCP endpoint indefinitely. Bound provider startup, crash restart, request concurrency, and output sizes. A provider crash degrades semantics for that provider, not raw viewing or unrelated languages. Do not download or enable executable workspace integrations as a side effect of opening a file.

### 15.6 Neovim and the debugging screen

Neovim can render annotations through extmarks, virtual text/lines, and signs [E-NVIM]. The bridge should own a dedicated namespace and clear only its own decorations. Use source-map coordinates, never display columns containing inlay hints, to place marks. Implement the requested rectangle as EOL virtual text; virtual hints inside a line are opt-in.

Map detailed types to hover or an explicit detail view. Map error details to virtual lines or a popup. The shared projection model also drives the Simple debugging screen's source, stack, variables, diagnostics, changes, and configuration panels. Each panel carries its source snapshot or stop epoch, so selecting a frame cannot silently leave stale values next to new source.

The editor owns actual buffer text and undo history. The viewer owns projection state. Synchronizing agent folds, moving the user's cursor, opening windows, and replacing buffers require an explicit UI-follow mode. LSP document synchronization does not by itself give MCP access to Neovim's cursor, windows, or unsaved state; the editor bridge or shared document store must supply that relationship.

### 15.7 Integration with existing agent file readers

An MCP server cannot silently replace another application's `read_file`, `cat`, or patch tool. Integrate this viewer by documented agent configuration, a supported host hook, or explicit use of `source_open`. Keep an exact raw-read operation for editing and unsupported tools.

The existing `simple_read` should gain a versioned/profiled projection contract, or remain a compatibility alias while a new tool becomes the preferred reader. Do not change an existing raw-reading contract to folded text without migration. In agent instructions, teach only the short first-use workflow; discover advanced commands through `adv` rather than copying the entire tool manual into every prompt.

## 16. Editing and replacement transactions

### 16.1 Source-edit lifecycle

Use this transaction state machine:

```text
proposal -> resolve original snapshot/ranges -> preflight -> preview
         -> authorize -> recheck versions -> apply -> reanalyze -> receipt
                              |
                              +-> stale/conflict: no silent application
```

An edit carries workspace/file identity, exact expected snapshot or document version, raw source ranges, replacements, and optional expected old bytes. Symbol/node handles are resolved against the expected snapshot; they are not universal identities that survive arbitrary edits. A failed remap requires refreshed analysis.

Preflight checks overlap, permissions, URI/path mapping, line endings, source encoding, cross-file references, and action applicability. Never derive an edit by stripping `▌`, `|`, line prefixes, or `/* ... */` from a rendered view. These strings may be legitimate source content.

### 16.2 Editor and filesystem ownership

For an open editor buffer, submit a versioned edit through the editor/document owner. Do not write the disk file behind unsaved changes. For a closed file, use the workspace edit coordinator and the common SOSIX file-publication mechanism. Preserve permissions and configured newline policy; do not rewrite unrelated bytes for convenience.

A single-file atomic replace does **not** provide a multi-file transaction. Use a workspace coordinator with preflight, ordered publication, journal/recovery, and a documented visibility boundary. For editor clients that cannot guarantee all-or-nothing workspace edits, disclose the limitation and verify every resulting version. Never report an entirely successful multi-file fix when only some edits were applied.

Concurrent agents must receive conflict results when expected versions differ. Do not allow last-writer-wins to overwrite another agent or the human editor. An undo receipt identifies its exact successor versions; undo cannot blindly revert subsequent independent work.

### 16.3 Verification after application

Refresh affected parser/semantic data and report diagnostics added, removed, changed, and not evaluated. Separate “edit applied,” “original diagnostic disappeared,” “build passed,” and “regression tests passed.” A build error may disappear because analysis failed; such a result is not verified repair.

A changed configuration file does not automatically authorize restarting a container, running a build script, or uploading a dump. Those are separate operations. Preserve source-edit and target-mutation audit trails independently.

### 16.4 Live replacement is a separate operation

A source patch changes a workspace snapshot. A REPL definition changes a session overlay. A native replacement changes an admitted runtime code generation. Keep these distinct, with explicit promotion between them.

Replacement previews include signature/layout/effect compatibility, retained old frames/objects, affected generic/macro/aspect dependencies, and restart requirements. Reuse the shared debugger's transaction rules [C01]. The source screen may display both running generation and edited source; it must not label an unbuilt edit as the code currently executing.

## 17. Performance and resource controls

### 17.1 Cheap views first, expensive facts on demand

A cached outline or display toggle must not spawn a compiler, run tests, enumerate every toolchain, walk Git history, or attach a debugger. Open from the shared source store, obtain structural information, then request only the annotations necessary for the view. Diagnostics can be displayed as cached/stale/pending; `check` is an explicit refresh operation when needed.

Reuse immutable parser results and dense/sparse side tables rather than duplicating source strings and ASTs for every agent. Build/test runners, LSP, MCP, and debugger clients can share immutable identities while retaining separate mutable client state. Use first-requester production with cancellation-safe waiters; cancelling one client must not destroy a shared computation still needed by others.

### 17.2 Bounded work and output

Every operation accepts deadlines, result bounds, and cancellation. Bound graph depth, visited nodes, alias expansion, source bytes, regex work, environment probes, external processes, and retained stop snapshots. Report whether a bound was reached. Avoid computing an enormous graph merely to truncate its serialized output afterwards.

The initial focused-view target is approximately **2,000 model-visible tokens**, configurable by client/task. This is a presentation target, not a completeness guarantee. Prefer coherent evidence units and explicit partial-context markers over cutting a source line or JSON object. A token estimate must be labeled when the client's tokenizer is unknown.

Pagination cursors bind to query, snapshot, provider generation, and access scope. New edits either preserve the frozen query or invalidate its cursor explicitly. Do not quietly mix pages from different snapshots.

### 17.3 Provisional performance objectives

These are engineering targets to validate on a documented reference machine, not measurements of current Simple:

| Operation | Initial warm-path target | Measurement conditions |
|---|---|---|
| Toggle `num` / `info` / `hint` | p95 below 20 ms service time | Existing projection; excludes network/client rendering |
| Local outline open | p95 below 100 ms | Cached source/parser; bounded outline |
| Focused source navigation | p95 below 200 ms | Cached semantic index; no cold provider startup |
| Annotation detail | p95 below 200 ms | Cached diagnostic/type/history fact |
| Expensive flow/history/environment query | Bounded, cancellable, progress-aware | Report first-result and total latency separately |

Benchmark cold and warm paths separately and record hardware, compiler build, corpus size, language mix, provider versions, and cache state. Do not promise universal numbers across remote targets or debug adapters.

Load tests should include 3,000 concurrent distinct query/cache keys as a stress profile compatible with the earlier cache direction, not as an assertion that 3,000 live debugger targets are required. Measure memory per view, retained snapshots, cancellation cleanup, queue fairness, and p99 latency under shared-cache contention.

### 17.4 Degradation behavior

If the semantic provider is unavailable, preserve raw/structural browsing and display the limitation once at the relevant boundary. A failed compiler process must not return “clean.” A failed history probe must not return “unchanged.” A failed environment probe must not choose an invented default. Retry policies are bounded and observable.

## 18. Security and operational safety

### 18.1 Workspace trust and executable providers

Treat source, comments, logs, diagnostic messages, configuration, and retrieved history as untrusted data, not agent instructions. Opening a repository must not authorize code execution. Language-server integrations can invoke project machinery; Rust analysis, for example, has executable build-script/procedural-macro considerations [E-RUST]. Expose trust and execution policy explicitly.

External grammars, native parser libraries, language servers, debugger adapters, and toolchain probes require version pinning and an appropriate isolation policy. A sandboxed grammar runtime is an option, not a claim that all existing native Tree-sitter grammars are safe or that every platform already supports the same sandbox.

### 18.2 Access boundaries

Validate workspace roots, canonical paths, symlink traversal, URI schemes, container source maps, and remote host identities. A detail handle must be bound to the principal/workspace that created it. Agent session IDs are identifiers, not bearer authorization by themselves.

Do not leak one subagent's buffers, credentials, current requester location, or runtime values into another session. Existing server-global requester defaults must migrate to the session/document model. Control of a shared debug target requires an explicit lease; read permission does not imply permission to resume, evaluate with effects, set variables, replace code, or terminate.

### 18.3 Safe rendering and data handling

Escape terminal control sequences and misleading display controls in presentation without corrupting the authoritative raw source. Preserve a reversible display map for escaped characters. Limit strings, object expansion, stack depth, and recursive values. Mark truncation and unavailable/optimized-out values distinctly from null or empty values.

Redact secrets before indexing, summarization, or transmission. Protect local caches and evidence bundles with scope-appropriate access controls. Remote inspection uses authenticated transport and explicit workspace/target authorization. Dump upload follows the per-application SDF policy from the shared debugger plan, not a default-on MCP side effect [C01].

### 18.4 Mutation and automation policy

Default source viewing and configuration explanation are read-only. Automatic fixes require trusted, deterministic applicability plus an enabled policy; speculative fixes require review. Running a proposed command, installing a compiler, changing OS/container settings, and deploying a patch are separate privileged actions.

Keep original failure evidence immutable. Record every mutation, test rerun, replacement generation, and verification result. LLM-generated explanations are hypotheses unless linked to supporting evidence; they cannot change the underlying diagnostic or execution record.

## 19. Incremental delivery and ownership

### 19.1 Delivery principle

Ship useful vertical slices. A reliable folded viewer and truthful diagnostics should not wait for whole-program slicing or native replacement. Conversely, a polished screen must not mask placeholder debugger operations. Each phase includes public-interface acceptance tests and documentation updates before capability promotion.

| Phase | Work packages | Primary owner role | Exit evidence |
|---|---|---|---|
| **P0: truth and contracts** | Audit actual dispatch, registrations, schemas, source readers, diagnostic conversion, and debug adapters; establish capability states and reproducible fixtures | Tooling + QA, with compiler/debug owners | Unsupported paths no longer masquerade as successful empty results; pinned inventory and failing regression tests for identified bugs |
| **P1: source store and viewer** | Shared immutable snapshots, overlays, positions, session preferences, first-open help, folded/focused/raw projections, synthetic imports, ASCII/Unicode rendering | Source infrastructure + MCP/UI | First/second/navigation examples work through real MCP; no source changes from viewing |
| **P2: native and structural language coverage** | Simple/SDN/SHS native adapters; SHS dialect detection; C/C++/Rust/Python Tree-sitter structural providers; error recovery | Parser/language owners | All language fixtures can be inspected with accurate source mapping and honest syntax-only labels |
| **P3: diagnostic and editing reliability** | Reuse DiagnosticV1, fix deletion/multi-file/version bugs, integrate code-action preview/apply, unsaved editor buffers, Neovim decorations | Compiler diagnostics + editor tooling | Real diagnostics and fixes agree across compiler, MCP, and LSP; stale fixes cannot apply silently |
| **P4: semantic parity** | Resolved calls/references/types, real call hierarchy, generic/expansion provenance, external LSP broker, core editor operations | Compiler query + provider owners | Known callers/callees and type queries pass fixtures; unsupported edges remain explicit |
| **P5: configuration and change intelligence** | SDN observations, provenance/config-use graph, build/run context, Git/JJ/SCV adapters, time/ref/diff/impact queries | Build/configuration + VCS owners | Passing/failing context comparisons reproduce exact identities and preserve secrets |
| **P6: live debugging screen** | Shared REPL/debugger integration, real stop/stack/locals, runner-to-worker tunnel, assert entry, source/frame synchronization | Debug runtime + runner + UI | Same stopped interpreter target is inspectable through screen, REPL, and MCP before unwind; native capability independently tested |
| **P7: causal analysis** | Def-use/CFG, field-sensitive writes, aliases/effects, bounded slicing, observed write correlation, concurrency evidence | Compiler analysis + debug instrumentation | Static possible causes and runtime observed causes remain distinguishable and pass adversarial fixtures |
| **P8: evidence and replacement integration** | Dump source/config correlation and server workflow; interpreter then admitted native replacement interfaces | Shared debugger/evidence owners | Companion steps 2, 3, and 4 integrated without changing their safety rules or ordering |
| **P9: hardening and rollout** | Performance, protocol conformance, stress tests, migration profiles, documentation and observability | Cross-team QA + release owner | Release gates pass on the supported matrix; unsupported environments remain explicit |

P6 can begin after P0/P1 and the shared debugger's step 0; it need not wait for P7. P5 can proceed alongside P3/P4. P8's dump integration is useful before either replacement stage. “Native and structural” in P2 refers to parsing providers, not a guarantee of native debugger availability.

### 19.2 Binding relation to the shared debugger plan

| Companion step [C01] | Integration required here |
|---|---|
| 0: shared library, interpreter failure stop, runner tunnel | Bind source snapshot and actual worker/fiber identity; show failing frame and minimum Essential help if unseen |
| 1: general assertions, interpreter/native MCP | Replace placeholder tools with shared commands; synchronize source, stack, locals, REPL, and capability messages |
| 2: sassert capture, SDF upload, dump server | Capture source/build/config identities; open post-mortem views; isolate LLM repair work; clean rebuild verification |
| 3: interpreter replacement | Show session overlay/definition generations; invalidate relevant source/type/query views; preserve old objects and evidence |
| 4: native replacement | Show running build/code generation, compatibility decision, retained frames, and restart/migration requirements |

Do not implement a second evaluator, duplicate breakpoints, or a separate MCP-owned debug execution engine to accelerate the screen work.

### 19.3 Concrete initial backlog

| Task ID | Action | Initial integration point / dependency |
|---|---|---|
| MCP-001 | Record supported/partial/stub/error behavior for each front door; add capability contracts | Main MCP, LSP-MCP registrations, LSP loop, debug adapters |
| MCP-002 | Fix empty-file read distinction; introduce versioned source projection route | `src/app/mcp/main_lazy_diag_tools.spl` |
| MCP-003 | Remove mandatory full-file numbering and check execution from the new view path | Same reader; preserve explicit legacy profile |
| MCP-004 | Add immutable snapshot/overlay/range mapping service and change notifications | Shared source/parser/cache infrastructure |
| MCP-005 | Add logical agent sessions, first-open help, preference setters, session cleanup | Shared viewer state; replace global requester coupling |
| MCP-006 | Implement outline/focus/raw and synthetic import folding | Native outline + language-provider interface |
| MCP-007 | Implement structured annotations, rectangle/ASCII rendering, optional virtual hints | Shared renderer and source-map contract |
| MCP-008 | Replace lossy diagnostic/code-action conversion | DiagnosticV1 + `lsp_handlers.spl` |
| MCP-009 | Implement resolved incoming/outgoing calls and proper symbol preparation | Shared query service; remove empty hierarchy handlers |
| MCP-010 | Add SDN schema/provenance provider and dialect-correct SHS viewing | SDN span parser; SHS/native-shell seam and regression fixture |
| MCP-011 | Add C/C++/Rust/Python structural providers and trusted semantic brokers | Grammar registry; configured language-server adapters |
| MCP-012 | Route stack/locals/evaluate/control through real shared debug capabilities | `main_lazy_debug_tools.spl`, `DebugServiceV1`, existing adapters |
| MCP-013 | Add debug-screen/REPL source binding and test-runner failure tunnel | Shared debugger steps 0–1 |
| MCP-014 | Add environment observations and effective-config explanation | Host-config owner; native environment identity; runner receipts |
| MCP-015 | Add reproducible history queries and change annotations | VCS adapters and snapshot-to-symbol mapping |
| MCP-016 | Implement writes/CFG/def-use/slice incrementally with unknown boundaries | Simple HIR/MIR and optional external analysis providers |
| MCP-017 | Add workspace edit transactions and truthful verification receipts | Source/document owner, SOSIX publication, diagnostics |
| MCP-018 | Add Neovim bridge, conformance suite, golden views, and performance dashboard | Shared projection/annotation contracts |

New service placement must follow the repository's module ownership rules. Paths listed in §2 are inspected integration points, not instructions to create competing implementations beside them. Re-audit branch-specific source layout before assigning work.

## 20. Acceptance tests and release gates

### 20.1 Test policy

Write modern SSpec acceptance specifications before implementation, using the repository's current executable-spec conventions. Proposed locations are `doc/06_spec/01_unit/`, `doc/06_spec/02_integration/`, and `doc/06_spec/03_system/`, with final subpaths chosen by existing owners. These are placement suggestions, not claims that specific new test files already exist.

Unit tests may use controlled fixtures and doubles. System acceptance must invoke the real public protocol/runner/debugger route and real parsing/analysis/runtime for the claimed capability. An empty mock call graph cannot certify caller support; a manually fabricated stopped event cannot certify assertion interception. A platform not exercised is skipped/unsupported, not passed.

### 20.2 Required acceptance matrix

| ID | Scenario | Required observation |
|---|---|---|
| VIEW-01 | First successful open for agent A | Folded outline, numbers off, Essential help once, minimal footer |
| VIEW-02 | Second file and later navigation | No repeated first-use help; same preferences retained |
| VIEW-03 | Two concurrent first opens | Exactly one first-help emission; both valid views |
| VIEW-04 | Missing file, then successful open | Failure does not consume first-help state |
| VIEW-05 | New subagent B | Independent defaults, help state, requester, and navigation |
| VIEW-06 | Reconnect/resume and expired session | Authorized resume preserves state; expiry is explicit |
| VIEW-07 | Retried `num` operation | Desired setting applied once, not toggled twice |
| VIEW-08 | No-intent file open | All bodies folded; outline bounded; no accidental full-file dump |
| VIEW-09 | Definition navigation | Target plus enclosing context revealed; siblings folded |
| VIEW-10 | Import grouping, including noncontiguous imports | Accurate range sets, original ordering, relevant imports individually visible |
| VIEW-11 | Folded block contains an error | Aggregate error visibility and detail navigation preserved |
| VIEW-12 | `info`, `hint`, and `num` changed independently | No cross-setting changes or semantic-cache invalidation |
| VIEW-13 | Source contains literal `\|`, `▌`, `/* */`, Korean text | Exact raw text preserved; decorations never stripped as source |
| VIEW-14 | Long lines, tabs, CRLF, emoji/non-BMP text | Correct byte/protocol/display mappings; no split tokens |
| VIEW-15 | Empty file | Valid empty snapshot and view, not read failure |
| VIEW-16 | Bounded focused result omits necessary context | Explicit partial marker and functioning expansion handle |
| LANG-01 | Simple valid and incomplete source | Native parser/query reuse; errors retain navigable spans |
| LANG-02 | SDN comments, duplicates, schema errors, scalar groups | Source-preserving view; canonicalization does not erase evidence |
| LANG-03 | `.shs` fixtures with sh/bash/native configuration | Correct dialect or explicit ambiguity; no execution on open |
| LANG-04 | Shell parser imported with compiler frontend | Name-collision regression checked; no silent fallback labeled native success |
| LANG-05 | C/C++ macro, conditional include, target flags | Syntax view works; semantic result tied to compile context |
| LANG-06 | Rust cfg/features, generics, macro expansion | Provider context/provenance retained; executable expansion policy respected |
| LANG-07 | Python imports, decorators, dynamic attributes | Static uncertainty preserved; module not imported to inspect it |
| LANG-08 | Missing/broken foreign grammar or language server | Raw/structural fallback remains usable; missing semantics explicit |
| DIAG-01 | Warning with successful compiler exit | Warning displayed; not incorrectly labeled wholly clean |
| DIAG-02 | Analyzer timeout/crash/invalid payload | Analysis failure, not empty success or zero errors |
| DIAG-03 | Windows drive path and escaped/multiline strings | Structured locations and messages round-trip correctly |
| DIAG-04 | Multi-file labels and macro trace | Original provenance and all related ranges retained |
| FIX-01 | Replacement is empty text | Valid deletion appears in preview and applies correctly |
| FIX-02 | Multi-file/multi-replacement action | All replacements preserved with correct URIs and expected versions |
| FIX-03 | Source changes after action creation | Stale fix rejected or explicitly re-resolved; no silent overwrite |
| FIX-04 | Overlapping fixes or partial client application | Conflict/partial application reported; no false transaction success |
| FIX-05 | Preferred but unsafe action | No unattended application based only on preference flag |
| FIX-06 | Diagnostic disappears after analyzer failure | Not reported as verified repair |
| FIX-07 | Unsaved editor buffer differs from disk | Correct owner/version edited; disk does not override buffer |
| SEM-01 | Direct, recursive, method, indirect calls | Correct resolved/possible edges and explicit unresolved boundary |
| SEM-02 | Shadowed variables and same-named members | Symbol identity prevents unrelated references/writers being merged |
| SEM-03 | Alias write, field mutation, FFI side effect | May-write/effect distinction; unknown external effects retained |
| SEM-04 | Branch-dependent assertion and loop | CFG/data dependence visible; no invented feasible execution claim |
| SEM-05 | Concurrent access without sufficient ordering evidence | Possible race reported separately from observed event ordering |
| HIST-01 | Last-touch, touches-in-window, net diff | Different semantics produce correct labeled results |
| HIST-02 | Tag/ref moves after query creation | Frozen query remains pinned or explicitly refreshed |
| HIST-03 | Rename, deletion, merge, shallow repository | Mapping/limitations visible; no fabricated current line |
| HIST-04 | Worktree and unsaved changes | Distinguished from committed `~7d` changes |
| ENV-01 | Installed compiler differs from actual build compiler | Inventory, selection, and observed invocation separated |
| ENV-02 | Consumer-specific override beats general host value | Explanation follows actual owner precedence |
| ENV-03 | Host and container have different PATH/OS/config | Correct execution scope; host facts not substituted silently |
| ENV-04 | Secret values, denied probes, stale observations | Redaction, explicit denial, and freshness preserved |
| DBG-01 | Interpreter test assertion | Stop before unwind; actual worker/fiber frame available through shared service |
| DBG-02 | Screen, REPL, MCP inspect the same stop | Same debug identity, epoch, stack, locals, and source snapshot |
| DBG-03 | Target resumes while detail request is in flight | Stale epoch rejected or frozen evidence explicitly returned |
| DBG-04 | Actual target write triggers data watchpoint | Real writer location/event; not just debugger `set_variable` detection |
| DBG-05 | Watch configured after earlier write | No invented historical writer or prior value |
| DBG-06 | Optimized/stripped native executable | Missing/optimized-out/unwind limitations shown honestly |
| DBG-07 | Fatal crash | Minimal capture path; no unsafe interactive REPL/upload in handler |
| DBG-08 | Dump from different build/source | Mismatch flagged; read-only evidence not confused with resumable process |
| DBG-09 | Session-local replacement | Running generation shown; old evidence retained; original test stays failed |
| DBG-10 | Unsupported layout/ABI replacement | Typed rejection/restart requirement; no partial publish |
| CACHE-01 | Many agents request same immutable result | Single production where configured; no mutable snapshot sharing |
| CACHE-02 | Producer/waiter cancellation and failure | No poisoned entry, hung waiter, or false completed result |
| CACHE-03 | Failed `.rr` metadata publication | No trusted partial graph; required consistency recheck completes before reuse |
| CACHE-04 | Presentation-only toggle | No reparse/typecheck/build invalidation |
| PROTO-01 | Real MCP/LSP lifecycle and malformed input | Correct framing/errors, bounded resources, clean shutdown |
| PROTO-02 | Feature advertised but backend unavailable | Explicit unsupported/denied status; no placeholder answer |
| PROTO-03 | Cancellation, paging, provider restart | Snapshot/version/cursor semantics retained |
| SEC-01 | Path traversal, symlink escape, foreign detail handle | Access denied at the service boundary |
| SEC-02 | Malicious comments/log instructions or terminal escapes | Treated as data; no tool execution or control-sequence injection |
| SEC-03 | Two agents share a target | Authorized read access and serialized mutation lease; no accidental control transfer |
| PERF-01 | 3,000-key stress, repeated open/close | Bounded memory, clean resource release, documented latency distribution |

### 20.3 Representative end-to-end scenarios

**Scenario A: compile warning and safe deletion.** Given a real source file whose warning includes a safe deletion fix, the first open shows a folded outline and one-time help. Navigating to the warning shows `W1 fix:1` after the boundary. Preview contains an empty replacement. Applying against the same version removes only the intended source. Reanalysis reports the actual remaining diagnostics. The second file open has no repeated help and line numbers remain off.

**Scenario B: interpreter assertion and writer investigation.** A worker/fiber fails an assertion before its frame unwinds. The runner opens the common session. The screen and MCP show the same stack and value. A possible-writers query includes an alias writer; an observed-writer query returns evidence only if instrumentation captured it. Debugger mutation is receipted, and the original failed test remains failed. A fresh rebuild/rerun is the only clean verification attempt.

**Scenario C: configuration-only regression.** Two runs use the same code but different compiler/container settings. The environment diff identifies the actual selected compiler and winning override. The SDN view opens the relevant setting, with all unrelated groups folded. No code change is invented to explain the failure. Secret values remain redacted throughout indexing, view output, and evidence export.

### 20.4 Architecture enforcement

Add architecture tests that reject direct mutable-backend access from MCP/LSP/UI handlers, duplicate debug session registries, ad hoc source-text parsing in protocol handlers, private compiler caches with incompatible invalidation, and edit application against projection coordinates. Approved compatibility adapters delegate to shared owners and have removal criteria.

Require a provenance chain for promoted capabilities: test identifier → actual front door → provider/target → source/build identity → result/receipt. Do not use successful tool registration, compilability, mock responses, or stale reports as a substitute.

### 20.5 Release gates

A viewer-only release needs P0–P2 truthfulness and source-map/session tests; it must not advertise unimplemented semantics. A fix-capable release additionally passes P3 edit/diagnostic gates. A debugger-integrated release must pass real stopped-target tests for each advertised backend. External semantic providers are individually admitted, not covered by the fact that their grammar can parse.

Run the supported Linux/Windows/macOS and additional BSD/Simple OS lanes according to actual CI availability. Separate cross-compilation from runtime verification. Every skipped backend carries a reason and an unsupported/unverified capability status until executed evidence exists.

## 21. Experiments and measurable outcomes

### 21.1 Source representation experiment

The user-selected default remains **line numbers off**. Evaluate alternatives rather than claiming that numbered lines inherently improve reasoning. SWE-agent demonstrates the importance of agent-computer interface design, but that alone is not an isolated proof that line-number prefixes help every model or task [E-SWE].

Run a paired experiment with the same tasks, models, revisions, tool capabilities, and budgets:

| Variant | Representation |
|---|---|
| A | Exact raw source, no numbers or annotations |
| B | Same source, absolute line-number prefixes |
| C | Focused semantic selection, no numbers, bounded annotations |
| D | Same focused selection with numbers |
| E | Focused selection with optional virtual type/parameter hints |

First compare A versus B and C versus D using identical source ranges to isolate numbering. Separately compare raw versus focused retrieval. Control whether the model can request expansion; report both initial-response and whole-task token usage. Randomize task order and include repeated trials when model behavior is stochastic.

Measure correct bug localization, successful fixes, incorrect edit coordinates, accidental annotation insertion into code, missed relevant branches/imports, tool calls, total tokens, latency, and human review burden. Include incomplete syntax, overloaded names, macros, aliasing, configuration regressions, Unicode, and cross-file tasks. Report confidence intervals and failure categories, not a single favorable average.

### 21.2 Operational success metrics

Track actual versus claimed capability coverage, invalid/stale edit rejection, proportion of views that trigger expensive compilation, cache hit rates, memory per retained session, first-use-help duplication, diagnostic conversion fidelity, debug-source mismatch detection, and redaction failures.

The expected benefit of focused viewing is a hypothesis until measured. Reduced text volume must not come at the cost of hidden evidence or incorrect fixes. A useful release improves task outcomes or resource use without weakening correctness gates.

## 22. Migration checklist and risk register

### 22.1 Implementation handoff checklist

Before coding, pin the chosen branch SHA and regenerate the scoped capability inventory. Confirm the actual executable paths used by agent/editor configurations, because an unused module cannot prove the behavior of a deployed binary. Locate the current debugging-screen frontend and connect it to the shared contracts rather than guessing its module name.

Adopt the session/snapshot/source-map contracts first. Migrate one end-to-end reader and one diagnostic/fix path before expanding the tool catalog. Keep compatibility profiles documented, install no surprise editor mappings, and preserve raw access. Add target-side evidence only through the shared debug service. Finish each phase with executable specs, migration documentation, and truthful capability receipts.

### 22.2 Risk register

| Risk | Mitigation / admission condition |
|---|---|
| Registration is mistaken for implementation | Test real handler/provider chain; remove placeholder success paths |
| Syntax candidates are presented as semantic certainty | Provider levels, edge kinds, unresolved boundaries, scoped completeness |
| Folded/filtered context hides root cause | Omission ledger, aggregate diagnostics, expansion and exhaustive modes |
| Annotation text becomes source | Separate source/virtual segments; raw edit contract; contamination tests |
| Agent state leaks across shared connections | Logical per-agent sessions and authenticated ownership |
| Unsaved buffers diverge from disk | One document owner with versioned overlays and explicit mappings |
| Multi-file action is partially or incorrectly converted | Structured codec, all replacements, deletion tests, transaction receipts |
| Shell dialect selected from extension alone | Shebang/project dialect resolution and explicit ambiguity |
| Analysis runs untrusted build scripts | Workspace trust and executable-provider policy |
| Native optimized debug data is incomplete | Capability checks and explicit optimized-out/unwind limitations |
| Runtime values paired with wrong source/generation | Build identity, stop epochs, snapshot and generation pinning |
| Failed capture is treated as replayable state | Separate inspection/reproduction/replay capabilities and evidence integrity |
| Cost explosion from semantic expansion | Budgets, lazy providers, graph bounds, shared immutable caches |
| Recent commit blamed without evidence | Reproducible comparisons and hypothesis/confirmation distinction |
| Config precedence drifts between tools and runner | Shared owner resolver and actual invocation receipts |
| Secret leakage through views/history/indexes | Redaction before indexing, scoped storage, tested export policy |
| Old branch docs contradict implementation | Pin inspected evidence; re-audit target branch; no completion from docs alone |

### 22.3 Definition of done

A completed feature has a documented contract, real provider implementation, truthful failure modes, bounded resources, source/target identity checks, public-interface acceptance evidence, and client-visible behavior matching this plan. “No crash” or “tool exists” is insufficient.

The first useful milestone is deliberately modest: **open any supported file as a trustworthy folded outline, navigate to intended source, show real diagnostics after a clear boundary, preserve per-agent preferences, and never confuse generated presentation with editable code.** Subsequent milestones add semantic depth, environment/change evidence, and real stopped-target debugging through shared infrastructure.

## 23. References and evidence

### 23.1 Repository sources

All repository links below are pinned to inspected `main` commit `e93e2a7bed8d576ad81ec7d51e3d64c2338464f3`. Inspection was scoped to the ranges described in §2, not the whole repository or a running installation.

| Reference | Source and use |
|---|---|
| [R-SRC] | Main MCP source reader and diagnostic handlers; whole-file numbering, per-read checking, empty-file handling, and text diagnostics |
| [R-LMCP] | LSP-MCP entry point; registered tools, session-requester behavior, and declared protocol version |
| [R-LSPENTRY] | Application LSP entry point delegating to the shared server |
| [R-LSPLOOP] | Shared LSP dispatch loop and registered request routes |
| [R-LSPHAND] | LSP query handlers, including empty incoming/outgoing call handlers and query-backed hints/folding |
| [R-ACTIONS] | Same handler file, inspected code-action conversion and pull diagnostics |
| [R-DIAG] | DiagnosticV1 SDN schema, fix confidence, replacements, labels, and macro provenance |
| [R-MCPDBG] | MCP debug handler implementation; scoped placeholder behaviors |
| [R-DBGSVC] | Central debug service's session/authorization reference implementation |
| [R-DBGARCH] | Reconciled MCP/LSP/DAP architecture index and explicit incomplete migration boundaries |
| [R-OUTLINE] | Native Simple outline facade and heuristic/token-based dispatch |
| [R-DIALECT] | SDN normalized parser adapter and documented shell/compiler name-collision issue |
| [R-SHS1] | Repository `.shs` example declaring `/bin/sh` |
| [R-SHS2] | Repository `.shs` example declaring Bash |
| [R-HOST] | Host SDN configuration and documented precedence/consumer-specific overrides |
| [R-ENV] | Native build environment identity and captured environment fields |

[R-SRC]: https://github.com/ormastes/simple/blob/e93e2a7bed8d576ad81ec7d51e3d64c2338464f3/src/app/mcp/main_lazy_diag_tools.spl
[R-LMCP]: https://github.com/ormastes/simple/blob/e93e2a7bed8d576ad81ec7d51e3d64c2338464f3/src/app/simple_lsp_mcp/main.spl
[R-LSPENTRY]: https://github.com/ormastes/simple/blob/e93e2a7bed8d576ad81ec7d51e3d64c2338464f3/src/app/lsp/main.spl
[R-LSPLOOP]: https://github.com/ormastes/simple/blob/e93e2a7bed8d576ad81ec7d51e3d64c2338464f3/src/lib/nogc_sync_mut/lsp/main.spl
[R-LSPHAND]: https://github.com/ormastes/simple/blob/e93e2a7bed8d576ad81ec7d51e3d64c2338464f3/src/lib/nogc_sync_mut/lsp/lsp_handlers.spl#L340-L650
[R-ACTIONS]: https://github.com/ormastes/simple/blob/e93e2a7bed8d576ad81ec7d51e3d64c2338464f3/src/lib/nogc_sync_mut/lsp/lsp_handlers.spl#L650-L810
[R-DIAG]: https://github.com/ormastes/simple/blob/e93e2a7bed8d576ad81ec7d51e3d64c2338464f3/src/compiler/00.common/diagnostics/diagnostic_v1_schema.sdn
[R-MCPDBG]: https://github.com/ormastes/simple/blob/e93e2a7bed8d576ad81ec7d51e3d64c2338464f3/src/app/mcp/main_lazy_debug_tools.spl
[R-DBGSVC]: https://github.com/ormastes/simple/blob/e93e2a7bed8d576ad81ec7d51e3d64c2338464f3/src/lib/common/debug/service_v1.spl
[R-DBGARCH]: https://github.com/ormastes/simple/blob/e93e2a7bed8d576ad81ec7d51e3d64c2338464f3/doc/04_architecture/app/mcp/mcp_lsp_dap_index.md
[R-OUTLINE]: https://github.com/ormastes/simple/blob/e93e2a7bed8d576ad81ec7d51e3d64c2338464f3/src/compiler/10.frontend/treesitter.spl
[R-DIALECT]: https://github.com/ormastes/simple/blob/e93e2a7bed8d576ad81ec7d51e3d64c2338464f3/src/compiler/80.driver/parse_dialect_adapters_v1.spl
[R-SHS1]: https://github.com/ormastes/simple/blob/e93e2a7bed8d576ad81ec7d51e3d64c2338464f3/scripts/os/mkfs-dbfs.shs
[R-SHS2]: https://github.com/ormastes/simple/blob/e93e2a7bed8d576ad81ec7d51e3d64c2338464f3/config/t32/t32_tcp_ping.shs
[R-HOST]: https://github.com/ormastes/simple/blob/e93e2a7bed8d576ad81ec7d51e3d64c2338464f3/config/host/host_config.sdn
[R-ENV]: https://github.com/ormastes/simple/blob/e93e2a7bed8d576ad81ec7d51e3d64c2338464f3/src/compiler/80.driver/cache/native_build_environment_identity.spl

### 23.2 Primary external references

Protocol versions below identify the referenced contracts, not an assertion that they are the newest available versions. Implementations must negotiate supported versions and validate current provider capabilities.

| Reference | Source and design relevance |
|---|---|
| [E-LSP] | LSP specification: standard document, navigation, diagnostic, action, and capability boundaries |
| [E-LSP-ACTIONS] | LSP code-action specification: quick fixes, resolution, preferred actions, and fix-all semantics |
| [E-MCP] | MCP 2025-06-18 tools specification: schemas, structured results, resource links, and errors |
| [E-DAP] | DAP specification/change history: debug capabilities, stopped-target inspection, and data-breakpoint evolution |
| [E-NVIM] | Neovim API reference: extmarks and virtual decorations without editing source |
| [E-TS] | Tree-sitter overview: incremental concrete syntax parsing and error-tolerant structure |
| [E-TS-EDIT] | Tree-sitter advanced parsing: incremental edit/tree handling |
| [E-CLANG] | clangd compile-command design: analysis depends on compiler command/context |
| [E-RUST] | rust-analyzer security guidance: executable project machinery and trust considerations |
| [E-PY] | Pyright configuration: Python analysis environment and project settings |
| [E-CONTEXT] | Context Mode project: intent-focused retrieval of retained/indexed evidence; no performance extrapolation to Simple |
| [E-GITLOG] | Git log documentation: revision/time/history query semantics |
| [E-GITDIFF] | Git diff documentation: snapshot and working-tree comparison semantics |
| [E-SWE] | SWE-agent research: agent-computer interface design; not isolated proof of a line-number advantage |

[E-LSP]: https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/
[E-LSP-ACTIONS]: https://github.com/microsoft/language-server-protocol/blob/gh-pages/_specifications/lsp/3.18/language/codeAction.md
[E-MCP]: https://modelcontextprotocol.io/specification/2025-06-18/server/tools
[E-DAP]: https://microsoft.github.io/debug-adapter-protocol/changelog.html
[E-NVIM]: https://neovim.io/doc/user/api/
[E-TS]: https://tree-sitter.github.io/tree-sitter/
[E-TS-EDIT]: https://tree-sitter.github.io/tree-sitter/using-parsers/3-advanced-parsing.html
[E-CLANG]: https://clangd.llvm.org/design/compile-commands
[E-RUST]: https://rust-analyzer.github.io/book/security.html
[E-PY]: https://github.com/microsoft/pyright/blob/main/docs/configuration.md
[E-CONTEXT]: https://github.com/mksglu/context-mode/blob/main/README.md
[E-GITLOG]: https://git-scm.com/docs/git-log
[E-GITDIFF]: https://git-scm.com/docs/git-diff
[E-SWE]: https://arxiv.org/abs/2405.15793

### 23.3 Prior project design

<a id="companion-plan-c01"></a>
**C01 — `simple_shared_repl_debugger_design_plan_2026-10-29.md`.** Prior user Library artifact, revision 1.0, dated 2026-10-29, based on the same inspected `main` SHA. Retrieved portions include mandatory requirements, steps 0–4, shared library/service ownership, failure preservation, replacement compatibility, and shared-cache/`.rr` policy. It is a proposed plan, not implementation proof. This document adds source-view, language-provider, protocol, diagnostic, configuration, and screen integration details without replacing its debugger contracts or delivery order.

[C01]: #companion-plan-c01

---

**Implementation priority:** truthful capabilities and shared snapshots first; useful folded views and diagnostic fixes next; semantic/environment/history depth and real shared-debugger integration incrementally; advanced slicing and admitted replacement only after their foundations are verified.
