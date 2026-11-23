# Blocked worker surface diagnostics

Executable spec: `test/01_unit/compiler/driver/worker_surface_gap_spec.spl`.

The failure owner already rejects a MIR target whose retained import/export
surface closure is incomplete. The diagnostic follows that same frozen graph
from the selected blocked target. It reports a reachable unbuilt surface or
invalid edge, without changing readiness or admitting any artifact.

| Scenario | Required observation |
| --- | --- |
| Unbuilt root | Identifies the root with zero examined edges. |
| Transitive missing provider behind a cycle | Identifies the actual `1 -> 2` edge; readiness remains unchanged. |
| Unrelated unbuilt surface and negative route | Does not blame an unreachable surface or invent an edge. |
| Fully built cycle | Terminates with no missing surface. |
| Invalid edge | Retains its actual index, labels the original blocking target, and avoids out-of-range access. |
| Search limit | Reports exhaustion explicitly; does not guess an unseen target. |
| Invalid root or absent edge row | Returns a diagnostic result without unsafe indexing. |
| Long paths | Caps each displayed path at 512 characters and labels truncation. |

The production search examines at most 256 edges. Only the blocking target and
the returned two indices are resolved to paths; no full path array is copied.
Batch-wide failure receipts explicitly name the original blocking target so a
sibling target is not mistaken for the owner of its edge. This is diagnostic evidence,
not a replacement for the original compile failure. A search-limit result does
not assert that a particular dependency is missing. Only failure paths invoke
the search; successful builds retain their existing behavior.

Verification must record actual executed/passed/failed counts and the tested
source/producer identity. A graph fixture pass does not establish that a new
compiler binary has been built or that the original bootstrap now succeeds.
