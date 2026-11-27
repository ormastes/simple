# MCP/LSP release/1.0.0 implementation audit

Baseline: `e2ce7042552`; inspected 2026-11-06. Source inspection only: no runtime admission inferred. Full downloaded plan read, including R01–R22, MCP-001–018, acceptance matrix and release gates.

## Existing implementation and defects

- `src/lib/nogc_sync_mut/lsp/lsp_handlers.spl:602–662` routes prepare/incoming/outgoing hierarchy to definition and call-edge query; no longer unconditional empty handlers. `lsp_call_hierarchy.spl` preserves resolution/partial markers. Semantic completeness and public execution still need qualification.
- `src/lib/nogc_sync_mut/lsp/lsp_code_action.spl` strict JSON codec accepts empty deletion, multiple edits, URI-keyed multifile edits and UTF-16 conversion. `document_edit` still sets version null; malformed edits can become title-only actions; non-URI multi-path edit sets rejected. No snapshot transaction guarantee.
- `src/app/simple_lsp_mcp/main.spl:201–203` exposes incoming/outgoing calls in addition to original tools; session requester remains process/server scoped.
- `src/app/mcp/main_lazy_diag_tools.spl:153–190`: empty file rejected, whole source numbered, check invoked for every read, successful warning suppressed. `parse_diag_text_line` first-colon parsing rejects Windows drive prefixes.
- `src/app/mcp/main_lazy_debug_tools.spl:250–290`: empty variables, synthetic main frame, echoed expression. Session registration is not runtime debug evidence.
- Search of src/app/src/lib/test at pinned revision found no SourceSnapshotStore, SourceProjectionService, ViewSessionState, source_debug_context or capability_audit implementation. Existing SCV source snapshots and parser/diagnostic/debug components are reusable infrastructure, not the requested shared viewer.

## Requirement ledger

| ID | Requirement | Current evidence/status |
|---|---|---|
| R01 | Cover Simple `.spl`, SDN `.sdn`, and SHS `.shs` as first-class source/configuration/script views. | Missing or unverified: no shared source-view public route found. |
| R02 | Provide the same structural viewing model for C/C++, Rust, Python, and additional registered Tree-sitter languages. | Missing or unverified: no shared source-view public route found. |
| R03 | Reuse native Simple parser/compiler/query infrastructure. Do not write competing parsers, type checkers, or debug evaluators in MCP handlers. | Partial: native query, call hierarchy and structured code-action helpers exist; shared snapshot service and runtime qualification missing. |
| R04 | First successful code open per agent or subagent shows Essential help once. Later opens show only the compact help footer. | Missing or unverified: no shared source-view public route found. |
| R05 | Line numbers are **OFF by default**. `num` toggles them; preferences persist for the entire logical agent session. | Missing or unverified: no shared source-view public route found. |
| R06 | Each subagent has independent preferences, help state, current view, and navigation history. Transport connections are not agent identities. | Missing or unverified: no shared source-view public route found. |
| R07 | A file open without a target/intent returns a bounded structural outline with all bodies folded, not the full file. | Missing or unverified: no shared source-view public route found. |
| R08 | Navigation opens the target and necessary enclosing context; unrelated bodies remain folded. This does not close human editor buffers/windows. | Missing or unverified: no shared source-view public route found. |
| R09 | Imports/includes/use declarations and other relevant non-block statements have synthetic fold groups with accurate source ranges. | Missing or unverified: no shared source-view public route found. |
| R10 | Generated end-of-line information starts after **`▌`** in Unicode mode; ASCII decoration mode uses **`\|`**. | Missing or unverified: no shared source-view public route found. |
| R11 | Optional in-code type/parameter hints may use display-only `/* ... */`; raw source and edit payloads never contain generated hints. | Missing or unverified: no shared source-view public route found. |
| R12 | Default footer is `[ess] [adv]`, not a toolbar repeated on every source line. Display preferences and advanced commands are available through help. | Missing or unverified: no shared source-view public route found. |
| R13 | Show concise errors, warnings, relevant recent changes, and active debug information. Expand explanations, types, provenance, diffs, and fixes on demand. | Missing or unverified: no shared source-view public route found. |
| R14 | Compiler/linter automatic fixes use canonical diagnostics and revision-checked edit transactions, with preview and explicit safety classification. | Partial: native query, call hierarchy and structured code-action helpers exist; shared snapshot service and runtime qualification missing. |
| R15 | Support callers/callees, reference/read/write classification, types, control flow, data flow, aliases, state changes, slices, and change impact, with capability and completeness labels. | Partial: native query, call hierarchy and structured code-action helpers exist; shared snapshot service and runtime qualification missing. |
| R16 | Distinguish static possible writers from runtime observed writers. Never invent write history that was not recorded. | Incomplete: synthetic MCP debug responses contradict shared stopped-target evidence. |
| R17 | Generate SDN environment/configuration observations and explain actual settings, selected tools, overrides, containers, OS/target identity, and build provenance. | Missing or unverified: no shared source-view public route found. |
| R18 | Support recent changes over a default seven-day window or a specified date/ref/tag range, resolved to reproducible boundaries. | Missing or unverified: no shared source-view public route found. |
| R19 | Integrate the same source view into the Simple debugging screen, REPL, DAP, MCP, test runner, assertion handling, and dump inspection. | Incomplete: synthetic MCP debug responses contradict shared stopped-target evidence. |
| R20 | Preserve the earlier order: test stop/tunnel → shared debugging/MCP → sassert/dumps/server → interpreter replacement → native replacement [C01]. | Incomplete: synthetic MCP debug responses contradict shared stopped-target evidence. |
| R21 | Keep expensive analysis lazy and bounded. Return explicit partial/unsupported/error states, not empty-success placeholders. | Missing or unverified: no shared source-view public route found. |
| R22 | Make all behavior testable through real public interfaces and modern SSpec acceptance specifications. | Missing or unverified: no shared source-view public route found. |

## Backlog mapping

| Task | Requested work | Status |
|---|---|---|
| MCP-001 | Record supported/partial/stub/error behavior for each front door; add capability contracts | Open; no completed shared-service route/evidence found. |
| MCP-002 | Fix empty-file read distinction; introduce versioned source projection route | Open; no completed shared-service route/evidence found. |
| MCP-003 | Remove mandatory full-file numbering and check execution from the new view path | Open; no completed shared-service route/evidence found. |
| MCP-004 | Add immutable snapshot/overlay/range mapping service and change notifications | Open; no completed shared-service route/evidence found. |
| MCP-005 | Add logical agent sessions, first-open help, preference setters, session cleanup | Open; no completed shared-service route/evidence found. |
| MCP-006 | Implement outline/focus/raw and synthetic import folding | Open; no completed shared-service route/evidence found. |
| MCP-007 | Implement structured annotations, rectangle/ASCII rendering, optional virtual hints | Open; no completed shared-service route/evidence found. |
| MCP-008 | Replace lossy diagnostic/code-action conversion | Partial: strict code-action converter exists; diagnostic reader remains lossy; version/transaction gaps open. |
| MCP-009 | Implement resolved incoming/outgoing calls and proper symbol preparation | Partial: hierarchy routes/query edges implemented; full resolved semantic fixture coverage/runtime admission unverified. |
| MCP-010 | Add SDN schema/provenance provider and dialect-correct SHS viewing | Open; no completed shared-service route/evidence found. |
| MCP-011 | Add C/C++/Rust/Python structural providers and trusted semantic brokers | Open; no completed shared-service route/evidence found. |
| MCP-012 | Route stack/locals/evaluate/control through real shared debug capabilities | Open; no completed shared-service route/evidence found. |
| MCP-013 | Add debug-screen/REPL source binding and test-runner failure tunnel | Open; no completed shared-service route/evidence found. |
| MCP-014 | Add environment observations and effective-config explanation | Open; no completed shared-service route/evidence found. |
| MCP-015 | Add reproducible history queries and change annotations | Open; no completed shared-service route/evidence found. |
| MCP-016 | Implement writes/CFG/def-use/slice incrementally with unknown boundaries | Open; no completed shared-service route/evidence found. |
| MCP-017 | Add workspace edit transactions and truthful verification receipts | Open; no completed shared-service route/evidence found. |
| MCP-018 | Add Neovim bridge, conformance suite, golden views, and performance dashboard | Open; no completed shared-service route/evidence found. |

## Acceptance ledger

Every scenario remains unadmitted pending its actual public-interface execution. Existing unit specs are not substituted for protocol/runtime evidence.

| ID | Scenario | Current evidence / remaining proof |
|---|---|---|
| VIEW-01 | First successful open for agent A | Open: Folded outline, numbers off, Essential help once, minimal footer |
| VIEW-02 | Second file and later navigation | Open: No repeated first-use help; same preferences retained |
| VIEW-03 | Two concurrent first opens | Open: Exactly one first-help emission; both valid views |
| VIEW-04 | Missing file, then successful open | Open: Failure does not consume first-help state |
| VIEW-05 | New subagent B | Open: Independent defaults, help state, requester, and navigation |
| VIEW-06 | Reconnect/resume and expired session | Open: Authorized resume preserves state; expiry is explicit |
| VIEW-07 | Retried `num` operation | Open: Desired setting applied once, not toggled twice |
| VIEW-08 | No-intent file open | Open: All bodies folded; outline bounded; no accidental full-file dump |
| VIEW-09 | Definition navigation | Open: Target plus enclosing context revealed; siblings folded |
| VIEW-10 | Import grouping, including noncontiguous imports | Open: Accurate range sets, original ordering, relevant imports individually visible |
| VIEW-11 | Folded block contains an error | Open: Aggregate error visibility and detail navigation preserved |
| VIEW-12 | `info`, `hint`, and `num` changed independently | Open: No cross-setting changes or semantic-cache invalidation |
| VIEW-13 | Source contains literal `\|`, `▌`, `/* */`, Korean text | Open: Exact raw text preserved; decorations never stripped as source |
| VIEW-14 | Long lines, tabs, CRLF, emoji/non-BMP text | Open: Correct byte/protocol/display mappings; no split tokens |
| VIEW-15 | Empty file | Contradicted by current MCP reader/formatter; assigned immediate repair. |
| VIEW-16 | Bounded focused result omits necessary context | Open: Explicit partial marker and functioning expansion handle |
| LANG-01 | Simple valid and incomplete source | Open: Native parser/query reuse; errors retain navigable spans |
| LANG-02 | SDN comments, duplicates, schema errors, scalar groups | Open: Source-preserving view; canonicalization does not erase evidence |
| LANG-03 | `.shs` fixtures with sh/bash/native configuration | Open: Correct dialect or explicit ambiguity; no execution on open |
| LANG-04 | Shell parser imported with compiler frontend | Open: Name-collision regression checked; no silent fallback labeled native success |
| LANG-05 | C/C++ macro, conditional include, target flags | Open: Syntax view works; semantic result tied to compile context |
| LANG-06 | Rust cfg/features, generics, macro expansion | Open: Provider context/provenance retained; executable expansion policy respected |
| LANG-07 | Python imports, decorators, dynamic attributes | Open: Static uncertainty preserved; module not imported to inspect it |
| LANG-08 | Missing/broken foreign grammar or language server | Open: Raw/structural fallback remains usable; missing semantics explicit |
| DIAG-01 | Warning with successful compiler exit | Contradicted by current MCP reader/formatter; assigned immediate repair. |
| DIAG-02 | Analyzer timeout/crash/invalid payload | Open: Analysis failure, not empty success or zero errors |
| DIAG-03 | Windows drive path and escaped/multiline strings | Contradicted by current MCP reader/formatter; assigned immediate repair. |
| DIAG-04 | Multi-file labels and macro trace | Open: Original provenance and all related ranges retained |
| FIX-01 | Replacement is empty text | Implementation present in lsp_code_action.spl and code_action_edit_roundtrip_spec.spl; actual preview/apply public route remains unverified. |
| FIX-02 | Multi-file/multi-replacement action | Partial structured multi-edit/URI handling; expected versions still null in converted changes. Public application missing. |
| FIX-03 | Source changes after action creation | Open: Stale fix rejected or explicitly re-resolved; no silent overwrite |
| FIX-04 | Overlapping fixes or partial client application | Open: Conflict/partial application reported; no false transaction success |
| FIX-05 | Preferred but unsafe action | Open: No unattended application based only on preference flag |
| FIX-06 | Diagnostic disappears after analyzer failure | Open: Not reported as verified repair |
| FIX-07 | Unsaved editor buffer differs from disk | Open: Correct owner/version edited; disk does not override buffer |
| SEM-01 | Direct, recursive, method, indirect calls | Call hierarchy query routing and partial/heuristic labels present; all resolved cases and public runtime evidence unverified. |
| SEM-02 | Shadowed variables and same-named members | Open: Symbol identity prevents unrelated references/writers being merged |
| SEM-03 | Alias write, field mutation, FFI side effect | Open: May-write/effect distinction; unknown external effects retained |
| SEM-04 | Branch-dependent assertion and loop | Open: CFG/data dependence visible; no invented feasible execution claim |
| SEM-05 | Concurrent access without sufficient ordering evidence | Open: Possible race reported separately from observed event ordering |
| HIST-01 | Last-touch, touches-in-window, net diff | Open: Different semantics produce correct labeled results |
| HIST-02 | Tag/ref moves after query creation | Open: Frozen query remains pinned or explicitly refreshed |
| HIST-03 | Rename, deletion, merge, shallow repository | Open: Mapping/limitations visible; no fabricated current line |
| HIST-04 | Worktree and unsaved changes | Open: Distinguished from committed `~7d` changes |
| ENV-01 | Installed compiler differs from actual build compiler | Open: Inventory, selection, and observed invocation separated |
| ENV-02 | Consumer-specific override beats general host value | Open: Explanation follows actual owner precedence |
| ENV-03 | Host and container have different PATH/OS/config | Open: Correct execution scope; host facts not substituted silently |
| ENV-04 | Secret values, denied probes, stale observations | Open: Redaction, explicit denial, and freshness preserved |
| DBG-01 | Interpreter test assertion | Open: Stop before unwind; actual worker/fiber frame available through shared service |
| DBG-02 | Screen, REPL, MCP inspect the same stop | Open: Same debug identity, epoch, stack, locals, and source snapshot |
| DBG-03 | Target resumes while detail request is in flight | Open: Stale epoch rejected or frozen evidence explicitly returned |
| DBG-04 | Actual target write triggers data watchpoint | Open: Real writer location/event; not just debugger `set_variable` detection |
| DBG-05 | Watch configured after earlier write | Open: No invented historical writer or prior value |
| DBG-06 | Optimized/stripped native executable | Open: Missing/optimized-out/unwind limitations shown honestly |
| DBG-07 | Fatal crash | Open: Minimal capture path; no unsafe interactive REPL/upload in handler |
| DBG-08 | Dump from different build/source | Open: Mismatch flagged; read-only evidence not confused with resumable process |
| DBG-09 | Session-local replacement | Open: Running generation shown; old evidence retained; original test stays failed |
| DBG-10 | Unsupported layout/ABI replacement | Open: Typed rejection/restart requirement; no partial publish |
| CACHE-01 | Many agents request same immutable result | Open: Single production where configured; no mutable snapshot sharing |
| CACHE-02 | Producer/waiter cancellation and failure | Open: No poisoned entry, hung waiter, or false completed result |
| CACHE-03 | Failed `.rr` metadata publication | Open: No trusted partial graph; required consistency recheck completes before reuse |
| CACHE-04 | Presentation-only toggle | Open: No reparse/typecheck/build invalidation |
| PROTO-01 | Real MCP/LSP lifecycle and malformed input | Open: Correct framing/errors, bounded resources, clean shutdown |
| PROTO-02 | Feature advertised but backend unavailable | Open: Explicit unsupported/denied status; no placeholder answer |
| PROTO-03 | Cancellation, paging, provider restart | Open: Snapshot/version/cursor semantics retained |
| SEC-01 | Path traversal, symlink escape, foreign detail handle | Open: Access denied at the service boundary |
| SEC-02 | Malicious comments/log instructions or terminal escapes | Open: Treated as data; no tool execution or control-sequence injection |
| SEC-03 | Two agents share a target | Open: Authorized read access and serialized mutation lease; no accidental control transfer |
| PERF-01 | 3,000-key stress, repeated open/close | Open: Bounded memory, clean resource release, documented latency distribution |

## Other mandatory deliverables

- capability_audit.sdn cross-product inventory not found; declared/routed/provider/tested/runtime-admitted must remain separate.
- P0–P9 all remain open as phases; P0 concrete truth defects identified, P3/P4 have prior partial implementation.
- Architecture enforcement tests, source maps, session ownership, transactional edits, external grammar/broker admission, stopped-target identities, environment/change provenance, Neovim bridge, stress/performance dashboard and migration profile require implementation/evidence.
- Proposed source interfaces: SourceSnapshotV1 (workspace, owner, URI, digest, original source, overlay version, language); SourceViewSessionV1 (principal, preferences version, help generation, selected view); SourceProjectionV1 (raw span/virtual segment maps, omissions, continuation, provider/completeness); avoid parser duplication and keep debug authority in DebugServiceV1.
- Full §21 A–E representation experiment and operational metrics are not evidenced. Cross-platform §20.5 gates require actual per-host/backend receipts.
- Companion shared REPL/debugger design is referenced but not available in Downloads under that filename; integration ordering remains required, not waived.
- Do not reproduce the downloaded plan’s outdated suggestion to put executable specs under doc/06_spec; repository rules place .spl under test/ only.

## Ownership

mcp_lsp_audit: main_lazy_diag_tools.spl and dedicated diagnostic specs/docs. Parent: shared service implementation planning, capability inventory, integration, runtime gates and landing. No memory lane edits.
