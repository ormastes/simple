# Host primary attachment settlement evidence refusal

Source: `test/03_system/app/orchestrator/feature/host_primary_attach_settlement_evidence_v1_spec.spl`

Requirements: ORCH-02, HOST-02. Status: NOT_RUN. Manually maintained source
companion; SPipe generation and maintenance scoring were not executed.

| Scenario | Intended result |
|---|---|
| Existing output-only evidence | Dispatch preserves the existing output validator, including corruption refusal. |
| Missing or corrupt selected domain | Refuse without trying another domain. |
| Correlated primary metadata | Retained signed admission and native metadata validate, but absent terminal proof prevents settlement. |
| Both consumed domains | Reject ambiguity even when the output marker is malformed. |
| Missing native archive and broker claim | Refuse without fabricating metadata. |
| Partial or symlink native archive | Preserve occupied entries and refuse recovery over them. |
| Substituted native identity or launch | Reject changed archived facts. |
| Forged canonical settlement | Missing actual terminal cleanup proof prevents capacity release. |
| Host-loss metadata recovery | Recover the missing native archive from existing broker metadata, but refuse settlement without terminal proof or with a changed consumption digest. |

Fixtures use real signature/admission and journal/file code with synthetic
broker claim/request metadata solely for refusal. The capacity gate must retain
CPU/memory charges and journal/ledger revisions on failure. No successful native
cleanup, session ownership, retirement, release, or cross-platform behavior is
simulated or claimed. Those positive and injected-failure boundaries remain
NOT_COVERED. See `doc/05_design/host_primary_attach_settlement_v1.md`.
