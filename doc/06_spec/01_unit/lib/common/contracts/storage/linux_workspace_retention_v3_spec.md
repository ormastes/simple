# Workspace retention V3 manual

Status: NOT_RUN for every authored case. No self-hosted compiler/test/native
campaign is authorized in this lane. These artifacts are not qualification.

| Requirement | Authored check | Evidence boundary |
|---|---|---|
| RETAIN-001 | Creation metadata excludes native retirement and quota-free fields; copied identities encode identically | Pure DATA only |
| RETAIN-002 | Ordered plan and actual receipt identity changes alter digests | Pure DATA only |
| RETAIN-003 | Exact image+working budgets+scratch and overflow rejection | Pure arithmetic, no allocation grant |
| SOURCE-V2-001/002 | Old/new strict codec separation and compiled layout binding with mandatory executable policy | Pure policy codec |
| Native partial failure | `check_partial_creation_retains_all_v3` asserts actual source diagnostics and generic-close refusal | Genuine fixture consumer, NOT_RUN |
| Native terminal/duplicate alias | `check_native_retirement_and_duplicate_v3` uses actual opaque token, repeated exact event and copied-source canonical state | Genuine fixture consumer, NOT_RUN |
| Wrong/stale token | `check_wrong_or_stale_actual_token_v3` requires an actual different or closed token and retained original owner | Genuine fixture consumer, NOT_RUN |
| Lower observer closed/WAL retry | `check_historical_metadata_after_lower_close_v3` materializes original retained event after genuine lower closure | Genuine fixture consumer, NOT_RUN |

The native fixture consumers live in test/fixtures/agent_workspace_retention_v3/scenarios.spl.
A real configured native XFS quota/Host fixture provisioning driver has NOT been
authored here. The caller must supply genuine actual owners and perform real
OCI/helper/transport/WAL gates; DATA constructors cannot substitute. Native
absence is never inferred for pre-subject failure. Full runtime qualification,
actual WAL recovery/charge persistence and separately authorized deletion
remain integration obligations of their owning lanes.
