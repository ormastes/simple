# SCV structural storage v1 acceptance contract

Scope: the explicitly requested first integrated syntax-storage slice of the
SCV master plan, sections 15–17. This contract does not admit production
performance, provider qualification or deletion of retained raw representations.

| ID | Required behavior | Executable evidence |
|---|---|---|
| REQ-SCV-STRUCTURAL-EXACT | The normal writer retains raw bytes, links a byte DAG, and restores exact bytes through the normal commit caller without a parser. Corruption or missing linked reconstruction fails before replacing a destination. | `test/03_system/app/scv/feature/scv_structural_storage_v1_spec.spl`, first scenario; unit tamper/schema/legacy cases. |
| REQ-SCV-STRUCTURAL-OPAQUE | Unsupported/unavailable/invalid provider results retain one explicitly opaque whole-file unit, with no new CDC map or fabricated parser execution. | System first scenario; unit provider-unavailable/opaque/empty cases. |
| REQ-SCV-STRUCTURAL-SPANS | Only validated complete host-tree spans set parsed boundaries. Preserve all gaps, repeats and exact byte lengths; reject overlapping ownership and error/missing-node ambiguity. Bound parser-free reconstruction. | System second scenario; unit overlap, exact-byte, dedup, giant-literal, retention and output-budget cases. |

All execution evidence is currently **NOT_RUN** because the checkout and source
workspace lack an admitted general-purpose self-hosted runtime. Test source
presence and static review do not establish these criteria as verified PASS.
