# Bug-linked workarounds

Selected scope: the user's 2026-09-30 request for temporary source workarounds,
bug links, recovery references, and cache-preserving builds. No open product
choice is required for this scope.

| ID | Requirement | Acceptance evidence |
|---|---|---|
| REQ-001 | A comment immediately before the affected block carries `@workaround bug=<canonical-id>`, optional `recover=<hex>`, and optional `reason=<text>`. | Parser accepts both `#` and `//`, validates IDs and 7–64 hexadecimal recovery references, rejects malformed annotations. |
| REQ-002 | Keep linked source locations in a textual derived database; the existing bug database remains authoritative for bug state. | Text round trip and joins by canonical bug ID; missing bugs reported. |
| REQ-003 | Update changed paths once at the parent build boundary. Explicit fullscan reconciles tracked paths. | Incremental add/edit/delete/revert, fullscan reconciliation, worker exclusion. |
| REQ-004 | Ordinary bug checks list indexed workarounds without scanning source. | Open bug displays links; fixed/closed bug flags review and recovery; optional bug filter. |
| REQ-005 | Missing/stale index is visible; branch/HEAD changes require explicit fullscan. | No implicit scan; malformed update preserves last valid index. |
| REQ-006 | Agents fix the owning bug, review linked blocks, restore intended code, and rebuild the smallest justified scope. | Documented recovery procedure preserves unrelated edits, cache identities, and required gates. |
| REQ-007 | Bootstrap/debug skills, cache guide, and SPipe host wiki describe the workflow. | Links and examples agree with the command/parser contract. |

The optional recovery hash identifies historical evidence. It never authorizes
whole-file checkout or automatic reversion. Workaround presence does not
resolve a bug or suppress a failed verification/admission gate.
