# MIR facet-cleanup manifest acceptance inventory

This inventory freezes the non-overlapping static acceptance owned by
`mir_cleanup_manifest_verifier_spec.spl` and
`mir_cleanup_manifest_roundtrip_source_spec.spl`. Executable compiler/backend
evidence is outside this static-only pass.

| ID | Acceptance case | Required result |
|---|---|---|
| MCM-001 | Two unconditional nested leases | Manifest and release sites consume inner then outer exactly once |
| MCM-002 | Guarded entry, present arm | Exact release site is consumed before the common continuation |
| MCM-003 | Guarded entry, absent arm | Continuation advances the same manifest cursor without executing the release |
| MCM-004 | Missing, duplicate, or extra release | `E-MIR-UNWIND003` |
| MCM-005 | Reordered release sites | `E-MIR-UNWIND003` |
| MCM-006 | Swapped or wrong-typed owner/lease operands | `E-MIR-UNWIND003` |
| MCM-007 | Wrong-typed presence local or stale guard/continuation | `E-MIR-UNWIND003` |
| MCM-008 | Join receives different entry cursors | `E-MIR-UNWIND003` |
| MCM-009 | Stale block, local, or instruction identity | `E-MIR-UNWIND003` |
| MCM-010 | JSON, function/body clone, and representative optimizer preservation | Manifest is byte-stable or identity-preserving; silent drop is forbidden |
| MCM-011 | Post-transform mutation before final backend handoff | Final production gate rejects the stale manifest before code generation |

Block labels are never proof identities. `entries` is the required execution
order, already reversed by lowering. A guarded entry names its Boolean presence
local, guard block, exact release site, and common continuation. All incoming
states at a join must agree on the next entry index.

The verifier may prove only the contracts represented in the manifest. Runtime
unwind personality behavior, source exception-packet identity, and executable
backend evidence remain separate release blockers.
