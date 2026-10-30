# CoreMux wire boundary source review — 2026-10-25

Status: **WARN / NOT_RUN — focused v2 source review complete; no open scoped P0/P1/P2 findings**. Independent source cycle 1 review of five boundary files at HEAD `61e47484277f98437f1f5090c94fb343bf51b4bc`. The six generated schema/value owners have a separate reviewer. Frozen CoreMux contract owners were not modified or re-reviewed. No compiler, test, native helper, product or transport process was launched by this reviewer; no production source was edited.

## Frozen source pins

All five hashes independently match `build/review/coremux-wire-codec-source-freeze-v1.md`.

| Path | SHA-256 |
|---|---|
| `src/lib/common/contracts/mux/wire_types_v1.spl` | `aa3bb9ad600337b379e16f1d088878a1dda34462caba2090ce2048b34b9801a8` |
| `src/lib/common/contracts/mux/wire_primitives_v1.spl` | `1f3f5702ea5db4783d7b93dc0a29d67841b6966528689cad9552f59ab950532f` |
| `src/lib/common/contracts/mux/wire_validation_v1.spl` | `04d618ff650c654dccd2fe7e5a666931e84118e59c05159358d5b4a0dd11d5be` |
| `src/lib/common/contracts/mux/wire_envelope_v1.spl` | `30caa798bde33ce6b0baf17d8af0ffcaaac31c579d2b28035f5de0a91ee7c34d` |
| `src/lib/common/contracts/mux/wire_exchange_v1.spl` | `f1c65c5da66842f6875e812327d947be9c33f902d7abd66a3f2eb072cc7f26b9` |

## Initial v1 findings (all source-closed by v2 below)

1. **P2: snapshot exchange ignores requested scope and visibility.** The `Snapshot(_, _)` exchange branch checks only returned handle and backend. A structurally valid snapshot containing unrelated session/window descendants or hidden/exited panes forbidden by the request therefore passes. Define the ancestors required for a coherent scoped snapshot, then require the returned descendants to belong to the requested Session/Window and apply its visibility flags. Namespace snapshots still require their requested visibility. The malformed reply must fail before the transport returns it as the requested success.
2. **P2: snapshot graph checks omit client context and restore-layout membership.** Client context is checked for owner/incarnation/kind only; it can identify a different client, missing object, or inconsistent session/window/pane chain. Restore-layout rectangles undergo bounded geometry and reference-shape checks but omit the same-window/existing-pane checks applied to active-layout rectangles. Reuse the established snapshot maps to reject these incoherent same-owner graphs, while preserving optional nil fields and the agreed scoped-ancestor policy.

3. **P2: sender byte preflight does not enforce the decoder's node ceiling.** A valid standalone Events response can fit the conservative 4 MiB size budget while exceeding 250000 SDN nodes. The schema reviewer derived an event-array example with 1024 increasing-cursor Notification events, each carrying 38 valid Client references in Rendered. With owner `a`, generation 1, unique IDs `c01` through `c38`, notification ID `a`, nil causal ID and observed revision 1, the array costs about 3,780,610 conservative bytes but 285697 SDN nodes, before the small batch/result/envelope overhead. The batch uses from=0, to=1024. The boundary event validator permits these counts and valid references; the public response encoder can emit it, but its own strict decoder rejects it. This is source-derived, not executed. Narrower request-specific PollEvents byte limits do not repair the standalone codec's round-trip/ceiling mismatch. Enforce the same structural budget during typed preflight before SDN construction, or conservatively refuse such inputs before encoding. Fixed schema nesting is shallow, but shared sender/receiver depth/node policy must remain explicit.

All three findings were sent to the contract author and parent before source changes. No authentication claim is inferred from adding graph checks: they only bind the reported representation to its request and other reported identities. The schema review's earlier 14000-client snapshot candidate was rejected because the snapshot validator caps clients at 4096; it is not evidence for this finding. The event example above satisfies the inspected standalone result validation.

## Boundary review

Public body entrypoints validate frame limits and typed calls/results, then invoke whole-value size preflight before allocating SDN values, byte-to-hex strings or canonical escaped output. The request envelope reserves auth/envelope space; response envelopes reserve their framing fields. The final actual encoded-length check remains a backstop. This boundary is distinct from internal `wire_values` helpers, which must not be called directly as allocation-safe transport entrypoints. Per-field UTF-8 conversion is bounded before the aggregate preflight; aggregate schema-size arithmetic is independently reviewed with the schema owners.

Primitive sums reject negative costs and costs exceeding the 4 MiB ceiling before addition. Text size bounds cap conversion and conservatively account for the canonical encoder's quote/backslash/newline/tab/carriage-return escapes; no six-byte Unicode escape expansion is assumed by that encoder. Byte payloads are capped at 1 MiB before hexadecimal expansion. The lowercase hex decoder rejects odd length, uppercase spelling and non-hex digits. Full-range u64 uses decimal text rather than signed SDN Int; its decoder rejects nondecimal/leading-zero spellings and checks the maximum quotient/remainder before multiplication/addition. i64 and u32 retain typed/range checks.

Frames use exactly four big-endian length bytes; only positive bodies within negotiated 4096..4194304 limits are accepted. The four-byte accumulator fits i64. Body decoding calls the established strict SDN byte parser with source bytes, depth 64 and 250000 nodes bounded before schema decoding; row/cell/column budgets are zero. The strict parser validates UTF-8, charges structural depth/nodes, rejects duplicate keys, and requires full consumption without permissive syntax recovery. The six-field envelope rejects wrong direction, zero/mismatched correlation, unknown status/call tags, result/call mismatch, and non-array/wrong-arity shapes. No dynamic Dict payload bypass is added.

Exchange validation binds connect backend/namespace and negotiated discovery limits; normal reply handle/owner generation; execute/disconnect request IDs and retained receipt operation; capture target and byte cap; current-context client; event owner/from-cursor/count and declared encoded budget. The initial snapshot gaps are corrected in v2 as recorded below. Failure outcomes use their actual commit evidence; Unsupported cannot claim applied effects or pending cleanup. Failure request-ID/affected-owner binding remains a transport obligation, rather than a standalone shape check being misrepresented as authentication. The in-progress client interface has explicit checks for those fields; its complete ownership/cleanup review belongs to the transport reviewer.

Static error codes avoid copying peer auth/pane data into codec errors. Peer-provided capability/evidence records and process IDs are representation only, never qualified evidence or proof of endpoint, lease, child, or receipt-ledger authenticity. No default success/provider implementation, new listener, implicit legacy-line compatibility, or automatic backend fallback is present in this boundary.

## Outstanding evidence

Executed codec/native/SSpec cases: **0**. Byte/node budget symmetry is corrected in v2 as recorded below. The six schema/value owners received their own source review; this report does not replace its pins or scope. The sixteen focused codec controls received the source review below and still require actual admitted-runner execution. Actual wire exchange, endpoint authentication, retry/reconciliation, resource ownership and application/backend qualification remain unexecuted. Source acceptance cannot replace these gates.

## Focused v2 correction review

All eleven owned source/spec/manual/design hashes independently match `build/review/coremux-wire-client-complete-freeze-v2.md` and the corresponding codec source freeze. The old six value encoders remain unchanged and their earlier inventory was not repeated. All three v1 P2 findings are closed at the source level. No open scoped P0/P1/P2 finding remains.

**Scope and graph:** exchange now applies a dedicated scope validator after matching handle/backend. Namespace observations obey visibility flags. Session observations contain exactly the requested session and its descendants; Window observations contain exactly the requested window and parent session, with matching panes/client contexts. Hidden and Exited panes are rejected when excluded. Documentation requires references and layout rectangles outside a projection to be omitted without reflow. Snapshot graph checks now validate client self-reference, existing session/window/pane membership and every supplied ancestry relationship, while retaining nil optional members. Restore-layout rectangles receive the existing-pane/same-window check already applied to active layout.

**Node and depth budgets:** the three new owners contain ninety-one typed counters corresponding to the existing record/variant/optional/array shapes. Source comparison checked each counter's field/case traversal against the already-reviewed size traversal, with independently specified node rules: scalar/null = 1, record/variant = array plus tag (2) plus payload nodes, Some = 2 plus payload, collection = 1 plus elements. Eighty-nine normalized formulas matched mechanically; the two apparent differences were the review transformation renaming the actual `value.size` field, and both actual functions were manually confirmed correct. This was source analysis, not an executed codec test. All variants and nineteen optional/array helper paths are covered by this correspondence; there is no default-zero count.

Each accumulation checks the 250000-node ceiling before addition. Request, successful response and failure response preflight add six nodes for the envelope root and five scalar fields, before semantic graph validation, SDN construction, hex expansion or canonical encoding. Arrays still enforce their declared element cap. An independent source call-graph calculation found maximum envelope nesting 9 for requests, 13 for successful results, and 6 for failures, matching the declared worst-case depth 13 below the strict parser's 64. This is an acyclic frozen-schema property, not a measurement or permission to add deeper schema without updating the bound.

The reported high-node event response now reaches `node_budget` refusal before constructing its SDN representation. Large byte payloads count as one encoded string node and retain their separate byte ceiling; the repair does not disable the intended 1 MiB binary case by lowering the global frame limit.

## V2 focused codec control review

Sixteen authored cases, **zero executed**. They call the actual public request/response encoder/decoder, strict parser, framing functions, primitive checks, graph/exchange validators and node/byte counters. Controls include all thirty command round-trips with maximum u64 correlation; numeric spelling/overflow rejection; literal binary and 1 MiB input; UTF-8 with independent numeric-byte oracle; malformed UTF-8, tags, arity, Dict bypass and trailing input; independently specified four-byte headers; frame/capture bounds; full state and all query/result shapes; Partial/Unknown preservation and contradictory Unsupported refusal; graph/scope negatives; and the byte-fitting high-node regression.

The high-node case first asserts semantic validity and byte-budget fit, then separately requires node refusal and the public encoder's exact `node_budget` code. The last case compares typed preflight count plus six against `document.nodes` from the actual strict parser on an admitted complete response, rather than comparing two copies of the same counter. The Korean/emoji fixture has explicit returned UTF-8 bytes. These are independent or production-owner oracles appropriate to pure codec tests. Typed PIDs/leases/capabilities are explicitly untrusted data, never fake live providers or native evidence; NotRun evidence is retained and asserted. The spec acquires no process/endpoint resources requiring cleanup.

The manual agrees with all sixteen case descriptions and marks source-authored documentation/docgen NOT_RUN. The reviewed design sections describe the corrected preallocation and projection rules, keep authority separate from representation, and retain actual endpoint/runtime prerequisites. The separate nine client and three endpoint scenarios are owned by the transport reviewer; this report does not duplicate or admit them.

### Final v2 owned pins

| Path | SHA-256 |
|---|---|
| `src/lib/common/contracts/mux/wire_types_v1.spl` | `aa3bb9ad600337b379e16f1d088878a1dda34462caba2090ce2048b34b9801a8` |
| `src/lib/common/contracts/mux/wire_primitives_v1.spl` | `1f3f5702ea5db4783d7b93dc0a29d67841b6966528689cad9552f59ab950532f` |
| `src/lib/common/contracts/mux/wire_validation_v1.spl` | `ecb801f3e7b04dde7f5d086709228d726d9da9be21a8958169ccc9e0ad6eecb8` |
| `src/lib/common/contracts/mux/wire_envelope_v1.spl` | `6e578c3c5619cbfb200b450c945a3a28ad5b1510f67d0d27555be7d2a9b951d1` |
| `src/lib/common/contracts/mux/wire_exchange_v1.spl` | `e8265908efd5020dc799a4bdba92683019e5785fe9f07a67878a01ff98508f7a` |
| `src/lib/common/contracts/mux/wire_budget_01_v1.spl` | `0287121b39ec6221821d4dc8bf6d9a796aaabf465f9dee3ffc3276045adc515d` |
| `src/lib/common/contracts/mux/wire_budget_02_v1.spl` | `31d3cfe7f67584db77ba3bb60b75d3ae7311940400e16c1e0ed356e1ae2fa09f` |
| `src/lib/common/contracts/mux/wire_budget_03_v1.spl` | `793a865efaced2aab67f00520d3fc2703e43cdae99ffe67c1ed1bc7820a32fcd` |
| `test/01_unit/lib/common/contracts/mux/wire_codec_v1_spec.spl` | `584d482f4f4147ba18d4811214bbe4cf95184410c996dffe09ae729a07832d47` |
| `doc/06_spec/01_unit/lib/common/contracts/mux/wire_codec_v1_spec.md` | `ce30142c939be2a40c5537c5646c8a85e310c1f1d418f610cbb18019d9f1f00c` |
| `doc/05_design/caret_mux_wire_sosix_v1.md` | `a9cb4dbe77ef0215ce6b0fa65108a9b779d661eecb459390998f62be14d12867` |

## Publication byte normalization review

Independently compared all ten retained originals under `build/review/sdk-eof-normalization/before/` with their live files and the receipt `doc/09_report/coremux_sdk_publication_normalization_2026_10_25.sdn` (SHA-256 `675d1a2bc1303f92bc1ceb3a0cbe926d199c0e03986b2dd5e00ce7a36c55e7cb`). Every before/after hash matches the receipt. Each live file is an exact byte prefix of its original, with exactly one trailing blank CRLF removed and one final CRLF retained. Both versions decode as strict UTF-8; every retained byte, including any BOM, line body and interior line ending, is unchanged. No mismatch was found. The receipt's ten after-hashes are the publication pins; historical review pins above remain intact.

All nine source originals match the complete v2 freeze: three budget owners and six separately reviewed value owners. The design original instead matches the later endpoint v3 pin `c95a317b5371a7ef0d35c6ca8c353552250564e7283e769c3eaa66a738a659da` in `build/review/coremux-endpoint-spec-freeze-v3.md`, covered by the cycle3 section of `coremux_sosix_client_source_review_2026_10_25.md`. That subsequent endpoint amendment is distinct from this normalization and does not replace the historical v2 design pin.

This check used only read-only byte/hash analysis. It adds no behavioral or runtime evidence: no schema review, green test, compiler, native helper, product or SSpec execution was repeated. STATUS remains **WARN/NOT_RUN**, with no open finding in this cosmetic publication scope.
