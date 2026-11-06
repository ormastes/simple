# Source-view detail design

Status: source/test authoring, execution unverified.

The common contract distinguishes snapshot identity, half-open UTF-8 source ranges, provider nodes with stable parent-array indices, folded range sets and source-contract results. Node indices are snapshot-local; qualified names are syntax lookup candidates, not durable semantic IDs.

`source_project_ranges_v1` rejects reordered/overlapping/out-of-bounds/split-UTF8 spans and records every omission. `source_project_raw_v1` pages whole lines, preserves CRLF/no-final-newline and rejects lines larger than the budget. Empty snapshots are valid.

`source_native_outline_v1` uses the canonical native token parser, not query CLI line heuristics. It converts function/container/member/import spans and reports parser diagnostics with source ranges. Container headers show their first grammar header line, leaving body docstrings folded. A native inline-body boundary repair stops at logical newline while preserving existing nested body/asm/opaque-block behavior.

`source_project_structure_v1` stable-sorts indices without changing parent identities, validates parent ordering, groups imports as range sets, and selects depth-one/two outline or unambiguous focused target plus enclosing context. Selected units are indivisible under budgets; pagination is explicit. The service hashes source/query settings into continuation identity. Changing source, mode, target, depth or limits invalidates the cursor.

`app/source_view/service.spl` parses strict typed JSON, admits bounded regular UTF-8 files and returns SourceOpenResultV1(payload,is_error). The payload contains no MCP envelope. MCP validates/caps IDs before source work and budgets both success and fallback output. Authenticated HTTP calls the same bound service and owns workspace authority and atomic success/first-help commit. The service reports unavailable hint/info providers rather than generating placeholders.

Preference transitions remain versioned desired-state changes with 64 bounded replay receipts. First-help is consumed only by the authenticated owner after a successful response fits its transport budget. Display labels and exact source remain separate fields.

Specs: source_view_foundations_spec, source_native_outline_spec, source_open_contract_spec and source_structure_service_spec. Exact native regressions include inline followed declarations, adjacent methods, nested multiline bodies, asm/opaque blocks, class docstrings and Unicode. Service regressions cover default folding, focused methods, noncontiguous imports, query-bound cursors, bound display/source separation and oversized/invalid JSON-RPC IDs. None has a runtime receipt yet.

Pending: admitted execution, real protocol lifecycle and authenticated concurrency evidence, generated/manual review and maintenance scoring, performance/resource calibration, and the full selected-plan requirements beyond this slice.

Bound service calls carry the authenticated owner's explicit canonical `workspace_root`; they do not reread process cwd after authorization. The unbound local MCP path captures cwd once. Descriptor-relative protection against malicious directory replacement remains a separate open IO requirement.

## Final static-review corrections

Each structural page includes all enclosing headers for every newly selected candidate. Ancestors are deduplicated, source-sorted and charged to both byte/node budgets; cursors advance only over candidates, never repeated context. If one new node plus its mandatory context cannot fit, the service returns mandatory_context_exceeds_budget. Open parent structures no longer simultaneously claim their whole body is folded.

Structural cursor identity also binds the canonical digest of the already-produced outline (schema/provider ID, ordered nodes/ranges and visible diagnostics/status). This is result content identity, not compiler-build provenance; the latter remains unavailable and explicitly reported.

CoreLexer internal positions are scalars, but lexer_next_token calls lex_current_token_byte_span before the outline owner receives Token.span. The adapter preserves those existing byte offsets; adding a second conversion would corrupt Unicode locations. The exact regression asserts offsets after a Korean/emoji comment and inside an inline string, then checks a continuation page.
