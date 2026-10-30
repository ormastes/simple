# CoreMux exact metadata targets

REQ-CMUX-002/005. **AUTHORED / NOT_RUN: 18 cases, zero executed.** This manual is authored, not generated. Compilation, canonical SSpec execution and native qualification remain pending with the root execution owner.

Source: `test/01_unit/os/apps/smux/core_mux_targets_spec.spl`. Production: `src/os/apps/smux/core_mux_targets.spl`.

`target_setup` constructs two sessions, three windows, four panes and three clients as immutable metadata fixtures. Unknown/exited child observations are data only; no child, server, transport or provider is started. `target_check_resolution` checks the returned existing kind, ID, owner and generation. Refusal checks require the typed error, NotApplied, no affected objects and no cleanup claim.

The production signature is `core_mux_resolve_exact_v1(snapshot, namespace, handle, target, kind, context) -> Result<MuxObjectRefV1, MuxErrorV1>`. It compares the expected namespace and complete handle, validates the existing snapshot graph, then checks every supplied context reference and its ancestry. Shape checks never authenticate the lease: the eventual query owner must authenticate and enforce its own current authority/revision before using the result.

Stable IDs take precedence over labels. An existing ID outside search scope refuses, even when a different in-scope object's label equals that ID. Duplicate exact labels refuse ambiguity. Session names search the namespace. Window names/IDs respect the resolved context session. Pane titles/IDs respect resolved context window and session. Client IDs respect the candidate client's stored session/window context, without selecting only context.client. Supplied references are membership/ancestry checked, including rejecting Some(empty-ID).

Following root's pre-freeze coherence correction, missing search-context fields expand from a supplied client's stored canonical context, then from a supplied/resolved pane's actual window/session, then from a window's actual session. Contradictory supplied fields refuse; no reference is minted. A missing stored field may be provided explicitly if the resulting ancestry is coherent. This is expansion of existing observations, not default-focus selection or authority: the resolver never chooses a session's current window or a window's active pane when absent from context. Client candidates with absent stored scope fields cannot satisfy a requested scope requiring those fields.

Pane-title matching is an explicitly generic convenience, not tmux CLI grammar. Labels are case-sensitive, untrimmed literal text; punctuation is not interpreted. Prefixes, numeric indices, relative selectors, composite tmux targets and implicit active targets remain pending adapter work. Clients have no label field. Hidden/exited objects may resolve only when present in the supplied snapshot; a returned reference proves neither liveness nor permission to mutate.

| Case | Production assertion |
|---|---|
| 1. Existing IDs | Each of Session, Window, Pane and Client returns its actual existing owner-bound reference. |
| 2. Unique labels | Session name can select another session; session scope and window scope disambiguate window names and pane titles. |
| 3. Duplicate labels | Repeated session/window labels and pane titles return InvalidTarget instead of a first match. |
| 4. ID versus peer label | ID wins namespace-wide; an out-of-scope ID refuses without falling through to an in-scope label. |
| 5. Siblings and isolation | Current window/pane permits sibling navigation within ancestors, while cross-session/window IDs refuse. |
| 6. Context membership | Missing references and inconsistent session/window/pane ancestry refuse even for session lookup. |
| 7. Typed context identity | Foreign owner, stale generation and wrong kind refuse despite matching ID text. |
| 8. Snapshot binding | Another namespace, lease token or owner generation refuses. |
| 9. Client scope | Another client in the same session can resolve; unrelated session/window and fabricated client labels refuse. |
| 10. Stored context, no defaults | Client-only context expands its actual ancestry; session-only context does not invent active pane selection, and empty targets refuse. |
| 11. Exact Unicode text | A Korean/emoji/punctuation label resolves exactly; prefixes, whitespace changes, uppercase, wildcard-like text, indices and newline refuse. |
| 12. Lifecycle boundary | A supplied hidden/exited pane resolves without changing lifecycle metadata, configuration revision or content revision. |
| 13. Malformed graph | Inconsistent pane ancestry and duplicate stable identity return InvalidRequest. |
| 14. Missing/kind mismatch | Window IDs cannot become Pane references; missing objects refuse and collection sizes remain unchanged. |
| 15. Ancestor expansion | Window-only and pane-only references disambiguate within their actual session/window, with cross-scope IDs refused. |
| 16. Client contradictions | Explicit session/window/pane values contradicting the supplied client's stored context refuse even when independently valid. |
| 17. Empty optional IDs | Some(empty-ID) in each of the four context fields refuses instead of behaving like nil. |
| 18. Candidate collection growth | A checked 35-window graph retains a late stable ID and unique label, while first/last duplicate labels still refuse. |

The helper performs bounded linear candidate scans after the existing common snapshot validator; it owns no registry, process, environment, file or network access. It does not mutate the snapshot, renew leases, drain output, publish revisions or implement the complete ResolveTarget operation. API/server composition and real consumer/process system scenarios remain required.

Source correction cycle 2 preserves the historical v1 manifest and addresses unchecked candidate append failure: the collection now returns Result, checks its independently counted length after every append and checks final length against the input collection before any match. An incomplete collection returns typed Unavailable with NotApplied and no reference. Context-membership construction propagates the same failure. This prevents silent truncation from erasing a duplicate and falsely establishing uniqueness. The new growth case exercises the actual resolver with independently checked fixture cardinality; it is not allocator failure injection. Allocation-failure execution evidence remains NOT_RUN and is not claimed by source checks or successful ordinary growth.

The root coordinator must run this exact source through the admitted canonical framework with retained producer/runtime/source hashes, emitted case count and failing/passing output. Interim Phase2 execution, if scheduled, must record the actual supported legacy library profile: the known producer does not support `--library-mode`. Native controls are not SSpec results; no new imitation framework or skip-to-pass fallback is permitted. Broader configured-profile, genuine Phase3, both-backend and N2 qualification remain separate requirements. No compiler, native build, test or helper launch was performed by this source author.
