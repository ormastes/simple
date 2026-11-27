# Fail-closed managed Host genesis

Status: SOURCE_ONLY / AUTHORED_NOT_RUN. This is a safety correction, not a
completed migration or a new positive admission capability.

An empty machine WAL records no charge; it does not establish absence of
legacy workloads or stop legacy writers. The actual Windows observer provides
`machine-boot-counter-v1`, which is not a native boot-incarnation proof. Current
Docker inventory lists the current provider label and returns one requested
physical-host/service-scope subset. Existing Host reconciliation correctly
requires retained charges and exact signed requests for every returned native
object under the same Host journal, but cannot account for every provider,
legacy service or unknown object across the whole machine.

The actual machine `managed_claim_v1` gate therefore refuses an empty WAL before
its first capacity commit. Historical recovery-only proof preserves the more
specific `machine-managed-claim-recovery-without-charge` error; fresh proof
returns `machine-managed-claim-migration-fence-unavailable`. The first-commit
branch is removed. Exact pre-existing durable charge validation and replay
remain in place. There is no new writer, second journal, positive marker,
readiness boolean, global prune or label-based adoption.

The production Host enrollment factory already retains machine cleanup before
calling admission. Refusal closes the actual machine writer and borrowed
native inputs or returns their retained cleanup owner. Deployment publication,
child creation and a provider observer using deployment-supplied policy follow
successful admission and are not reached by this denial. Actual installed
provider probes during machine-authority opening remain distinct from that
supplied-policy observation; zero engine execution is not claimed.

A positive producer remains a missing **source capability**, not merely a
missing external fixture. It must own actual whole-provider legacy-writer
exclusion and complete inventory, or exact owner-validated adoption retaining
every legacy charge. Its opaque capability must be consumed by the same
machine writer before genesis and remain valid through that first durable
charge. Scoped inventory, boot-counter equality, empty WAL, labels and caller
statements cannot construct it. The installer/service-manager ownership and
provider-wide inventory producer have not been implemented or qualified here.

The previously frozen six-file Host snapshot remains immutable historical
source. Its fresh-enrollment positive scenario is superseded: the worktree
retains the two native proof tests, removes the unreachable positive oracle,
and documents existing-charged recovery as NOT_COVERED without a genuine
retained fixture. The unique regression/manual
`windows_host_migration_genesis_guard_v1_spec` invokes actual signed Host
enrollment and requires refusal plus the unchanged actual empty machine WAL.
All scenarios remain NOT_RUN; no synthetic WAL rows are introduced as proof.
