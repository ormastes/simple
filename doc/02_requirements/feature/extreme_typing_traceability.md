# Selected extreme-typing addendum and traceability extension scope

Status: user-selected language constraints, 2026-11-01; implementation and
qualification pending. The user confirmed all raw true builtin types, including
text/char/bool, and domain-safe public generic bounds, explaining that easy type
creation is available. Do not reopen those policies as optional exemptions.

The existing selected `simple_traceability_sdn_slop` requirements/NFRs and their
20 REQ-TRC/40 AC-TRC IDs remain unchanged. The requested traceability, extreme
typing, LSP and Caret capability scope selects the extension below. Remaining
[group/changeset/coverage/migration choices](extreme_typing_traceability_options.md)
are implementation-policy blockers for dependent work only.

| Selected ID | Required extension behavior |
|---|---|
| REQ-TRC-021 | List/show feature groups, features, requirement groups, requirements and bugs over one explicit immutable snapshot. |
| REQ-TRC-022 | Canonical authored group IDs, typed membership, cycle detection and attributable migration. |
| REQ-TRC-023 | Indexed walk/path/impact/gaps use bounded traversal and snapshot/query/authorization-bound cursors. |
| REQ-TRC-024 | Bugs distinguish affected entities, reproducing tests and explicit fixing changesets. |
| REQ-TRC-025 | One pure TraceViewProjection supplies CLI, LSP, MCP, Slop, Caret, Markdown and HTML. |
| REQ-TRC-026 | Compiler-derived code relations carry canonical identity, expansion provenance and resolution precision. |
| REQ-TRC-027 | Feature-by-layer membership and layer dependency matrices are separate, sparse and honest about unknowns. |
| REQ-TRC-028 | Existing Slop shows requirements/code/API/bugs and preserves selection, snapshot and provenance. |
| REQ-TRC-029 | Git facts use repository+OID; PR metadata exposes freshness; inferred touches are not explicit implements/fixes. |
| REQ-TRC-030 | Caret overlays compare registered agents' base/head/staged/dirty snapshots; overlap is not a merge-conflict claim. |
| REQ-TRC-031 | Explicit deterministic report/export destinations respect visibility, safe paths and offline operation. |
| REQ-TRC-032 | API/type trace facts come from compiler-owned semantic surfaces and never decide type validity. |

| Selected ID | Required behavior |
|---|---|
| REQ-EAPI-001 | Check the effective externally exposed Simple API after canonical type and visibility resolution, including implicit/generated/reexported exposure. Private locals and implementation representation are not banned. |
| REQ-EAPI-002 | Deny every reachable bare true builtin integer, float, bool, text, char or platform-size scalar. Recurse through transparent aliases, arrays, tuples, unions, option/result/container arguments, callbacks and public fields. A nominal newunit/opaque boundary may hide private representation; its public operations cannot leak it. |
| REQ-EAPI-003 | `extreme_public_api` is advisory at moderate, warning at strict, fatal at robust/critical/verified. Legacy pure-math, allowlist or warning-phase exemptions cannot weaken this named rule; unrelated robust warnings retain existing semantics. |
| REQ-EAPI-004 | Functions/methods, constructors, getters, enum payloads, traits/associated types, globals, aliases, generic defaults, callbacks, module exports, `__init__` reexports and macro/AOP/postmono exports are covered before publication/initializers. |
| REQ-EAPI-005 | Native, interpreter, REPL, dynload, JIT and SMF share enforcement. Rejected REPL loads preserve the last valid state; denied loads run no user initializers or callbacks. |
| REQ-EAPI-006 | Unresolved types, invalid/unresolved alias cycles and over-budget exposure are Unknown, not Safe. Well-formed recursive nominal types receive SCC/fixpoint classification. Exposed generics require a semantic-domain-safe bound; substitutions and generated specializations are rechecked. Cache identity binds policy, semantic graph and exposed-surface digests. |
| REQ-EAPI-007 | Easy nominal type creation and existing typed literal syntax are first-class migration ergonomics. Keep raw FFI ABI private behind typed facades; no public raw constructor or getter may reopen the boundary. Check literal resolution, ranges and generated constructors rather than inventing syntax or assuming usability. |
| REQ-EAPI-008 | `api list/check/explain/violations/migration-plan` and trace API/type views expose the compiler's results and explain the export-to-primitive path. Planning is read-only. |
| REQ-EAPI-009 | Formal certification requires refinement to production IR and durable manually reviewed proof artifacts. Missing support is blocked; a lint result or unit test cannot assert proof. |

The named semantic-domain bound has no new syntax chosen here: reuse existing
constraint syntax if it can express the guarantee, otherwise design the minimal
explicit extension in E1. Phantom generic arguments also need policy-defined
domain safety; do not assume unused parameters escape checking. Raw pointers
and `any` remain separately classified unsafe exposure, never a primitive-rule
bypass.

This supersedes REQ-WUN-007's primitive allowlist for robust/critical/verified
public Simple APIs. Wrapping `i64` in `Option` or `Result` does not eliminate
the primitive leaf. Historical non-robust lint behavior remains distinct.

Acceptance and rollout are in the [system test plan](../../03_plan/sys_test/extreme_typing_traceability.md)
and [implementation plan](../../03_plan/agent_tasks/extreme_typing_traceability.md).
No executable acceptance result is claimed by this requirements selection.
