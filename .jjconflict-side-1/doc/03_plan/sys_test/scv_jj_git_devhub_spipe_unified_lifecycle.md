# Unified lifecycle system-test plan

Executable owner:
`test/03_system/app/scv/feature/scv_jj_git_devhub_spipe_unified_lifecycle_spec.spl`.

| Scenario | Requirements | Oracle |
|---|---|---|
| Stable change and immutable revision identity | REQ-001 | Same seed gives same ChangeId; changed tree/parent/metadata changes RevisionId |
| Exact review/gate binding | REQ-003 | stale revision rejects approval and incomplete evidence rejects bundle |
| Observe-only protected planning | REQ-002, REQ-008, REQ-010 | valid policy parses; stale CAS/approval refuses; exact evidence yields dry-run steps only |
| Three-way provider projection | REQ-004, REQ-005 | disjoint edit pulls/pushes; concurrent edit creates durable conflict |
| Immutable release | REQ-006 | publication requires identity; published release rejects rewrite and permits withdrawal |
| Entity separation | REQ-007 | typed values retain distinct IDs/relations |
| Compatibility/portability | REQ-009, NFR-002, NFR-007 | DevHub compatibility help remains and lifecycle command has versioned output |

The manual-visible primary flow uses the five frozen step phrases in the SPipe
state. Edge and rejection scenarios may be folded. No remote provider, Git ref,
or tag is mutated by this system spec.

