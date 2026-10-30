# Independent CoreMux typed wire values source review

Status: **WARN / NOT_RUN**. Source cycle 1. No scoped P0/P1/P2 finding was identified in the six frozen typed-value owners. This is source acceptance only, not codec execution, transport/provider qualification, command semantics or release admission.

Worktree: `D:/dev/simple-coremux-shared-20261025`. Declared freeze HEAD: `61e47484277f98437f1f5090c94fb343bf51b4bc`. Inputs: `build/review/coremux-wire-codec-source-freeze-v1.md` and `build/review/coremux-wire-schema-v1.md`. All six actual SHA-256 values matched the freeze before inspection. The five framing/primitive/validation/exchange owners are independently reviewed by the boundary reviewer; this report does not replace that review.

## Scope and method

The six owners contain 3,297 supplied source lines. Reviewed representative full implementations and every command branch, then performed an in-memory static comparison of all typed bodies against the independent frozen schema. That comparison derives expected record field order/helper type, enum tag/payload order, decoder arity/error propagation and size traversal from the schema. It does not execute Simple, construct runtime test evidence or substitute a copied predicate for the actual codec.

The schema has 41 records and 31 enums, with 188 total enum variants. All 216 size/encode/decode bodies for those 72 types matched the expected schema patterns. Eight optional types and eleven array types add 57 helper bodies; those matched the inspected null/some and bounded-array patterns. Cross-file typed helper references resolve to the inspected owner or an explicitly imported typed owner. No mismatches were returned. Seventy-one non-CapLevel declarations were additionally compared with their actual exported core/execution/observation/wire type declarations; CapLevel's actual canonical owner was inspected separately. This was interface verification, not another whole-contract review.

These are static inventory counts, not authored or passing test cases. No compiler, test, native process, helper executable, endpoint or product was launched. No production source was edited and no commit was made. The context-mode file sandbox had returned exit -1 earlier in this review lane; bounded PowerShell/in-memory processing avoided flooding raw source into the review context.

## Data preservation and strictness

- `wire_values_01_v1.spl:485-602` preserves Exec's executable and complete argv array separately from Shell's command string. Launch retains optional cwd, ordered Set/Remove environment changes and requested size. Empty strings, empty argv, absent cwd and an explicitly present empty cwd remain distinct. These codecs perform no quoting, interpolation, shell parsing, trimming or execution.
- `wire_values_03_v1.spl:13-280` has all 30 command variants with matching discriminants, field order and nested helper types in sizing, encoding and decoding. The set is CreateSession, RenameSession, TerminateSession, StopOwnedNamespace, CreateWindow, RenameWindow, TerminateWindow, FocusWindow, LaunchPane, SplitPane, TerminatePane, FocusPane, ResizePane, ResizeWindow, SelectLayout, ToggleZoom, HidePane, ShowPane, Rebalance, SetPaneTitle, SetPaneBorder, SetPaneBorderStatus, AttachClient, DetachClient, SetClientViewport, SendLiteral, SendKeys, Paste, SubmitShellCommand and Notify.
- Literal input and paste bytes use the binary helper, not the text/shell-command helper. Named/function/scalar keys and modifier flags keep their typed union payloads. Titles, notification literal text, cwd, argv and environment strings flow through strict text helpers without shell interpretation. Actual preservation of all Unicode and arbitrary byte values still requires native roundtrips.
- Observation and result records retain owner/generation identity, revision and request IDs, optional active/zoomed pane and restore layout, full rectangle arrays, child exit/unknown state, request knowledge/commit state, capability evidence, affected/created/changed references, notification receipt, cleanup flags and continuation tokens. No omitted field or substituted success/default was found. Wire call/result variants preserve the five connect/query/execute/poll/disconnect families; outer call-tag/correlation checks belong to the boundary owner.
- `wire_values_04_v1.spl:451-482` maps actual `CapLevel.Native`, `Emulated`, `Unavailable` to the canonical lowercase wire tags native/emulated/unavailable and back. Uppercase or unknown tag variants are not accepted.
- Every record decoder requests exact array arity and exact type tag before reading fields. Every enum decoder rejects an empty array, unknown variant or incorrect payload arity. Nested Result failures propagate through `?`; no fallback creates an unrelated/default successful typed value.
- Optional encodings are precisely null or two-element some arrays. Present-invalid payloads propagate an error rather than becoming absent. Typed arrays preserve order and empty arrays; sizing rejects counts above 16,384 and decoding uses the actual primitive array guard with the same cap before element conversion.
- Primitive interfaces were inspected only as dependencies: array/tag guards reject incompatible SDN kinds; bool/int/text remain distinct; u32 checks range; full u64 uses canonical decimal text; binary uses bounded canonical lowercase even-length hexadecimal. Dict/Table/Float are not accepted as a typed payload escape hatch. UTF-8 validation and byte/text allocation boundaries remain the boundary reviewer's qualification scope.

## Size and allocation boundary

Every size traversal visits the same fields/payloads as encoding, uses bounded addition and propagates child failures. Record and enum overhead estimates are conservative for their tags and delimiters. Optional and array wrappers account for their own overhead. Inner encoders intentionally return SdnValue directly and assume whole-envelope validation/preflight; they are not safe public transport allocation boundaries on their own. Callers must use the reviewed envelope entrypoints.

Separate boundary coordination identified a possible sender/receiver node-limit mismatch. The initial shape-only example with 13,000 clients was withdrawn because the boundary's semantic client cap is 4,096. The corrected candidate is an Events response containing 1,024 sequential events, each Notification(Rendered(38 same-owner Client references)): each event expands to 279 SDN nodes and has conservative size 3,538 bytes with short IDs. Its event array totals 285,697 nodes and 3,624,962 conservative bytes, leaving room below 4 MiB for the small batch/result/envelope while exceeding the 250,000-node decoder limit. The boundary reviewer must confirm admissibility and close the sender/receiver consistency issue; this report does not claim envelope acceptance merely from typed shape. Repeated rendered references were reported permitted by that reviewer. No executable probe was used.

## Evidence still required

Focused real codec specs and their review/execution are a separate gate. Require byte-level roundtrips and independent expected-wire oracles across all command/result variants; optional absent/present/empty distinctions; ordered argv/env changes; Unicode including multibyte scalars; literal NUL/non-UTF8 bytes; numeric boundaries; wrong primitive/arity/tag; nested errors; and frame/depth/node/count limits. Roundtrip alone can conceal a symmetric schema error, hence the independent schema comparison above and explicit wire expectations are both useful.

Authorization, lease/receipt authority, valid graph relationships, scoped object ownership, field semantics, launch execution, process lifetime and provider capability honesty belong to the owner/validation layers. Typed decoding is not authority. Actual Windows/native execution, transport tests, selected NoGC/provider compilation, generated manuals and coverage remain NOT_RUN. No provider parity or release PASS is asserted.

## Frozen reviewed SHA-256 values

| Path | SHA-256 |
|---|---|
| src/lib/common/contracts/mux/wire_values_01_v1.spl | `d7231399e829c01638115f6a8e218c21d707b5d892b08252e16ac17d1fe03fc5` |
| src/lib/common/contracts/mux/wire_values_02_v1.spl | `6e69235d75ce5ed1cf23ab4724181a8cdd952f305de393201f73095381649333` |
| src/lib/common/contracts/mux/wire_values_03_v1.spl | `600995725caa7b594bcb7020531d9602852365899df6346458dcb0b5476b1ed5` |
| src/lib/common/contracts/mux/wire_values_04_v1.spl | `23665cee0592c1e1794f4a7dd61871091f011287eb9d1c3baf7fb971eed8fb93` |
| src/lib/common/contracts/mux/wire_values_05_v1.spl | `8d8f8f0a1b5e86c2ba96bafaa42fc97b296de4ec3bbc28081d6e42be7af1a4d1` |
| src/lib/common/contracts/mux/wire_values_06_v1.spl | `643b6f4bae054fbde0efcb431e1558f2d2f0fd22ad5507f3c854424126d0bf6a` |

Frozen schema SHA-256: 6b20d696e024b886c13e2a919f2c71e30bfec401b865a3a4a855f218253f4c5f.

### Boundary confirmation after typed review

The independent boundary reviewer confirmed the Events example passes standalone semantic validation. Using 38 unique three-character client IDs c01..c38 per notification instead of repeated short IDs raises the event-array conservative estimate to 3,780,610 bytes while retaining 285,697 nodes. The small outer batch/result/envelope still fits the 4 MiB cap. This is a confirmed boundary P2, reported to the author/root; it does not change the six typed-field review conclusions. The exchange-specific 1 MiB polling budget does not repair the standalone public encode/decode mismatch. No runtime execution was performed.