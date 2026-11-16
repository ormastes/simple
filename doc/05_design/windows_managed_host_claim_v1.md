# Managed Windows Host claim composition

Status: SOURCE_ONLY / AUTHORED_NOT_RUN. Native export approval, compiler,
runtime, SPipe, docgen and disposable Windows fixture execution remain pending.
This adds a narrow delta to the retained Host deployment/local-root foundation;
it does not claim that pre-existing dirty work was authored by this lane.

The installed machine policy pins both the managed issuer and the exact
enrollment authority-policy digest. An issuer string alone cannot authenticate
caller-selected keys. `VerifiedHostServiceEnrollmentV3` borrows actual retained
native root/policy-file generations and exact metadata bytes. Its factory and
refresh verify native security, byte pins and the genuine signed enrollment
before deriving `credential.signed.issuer_id` and checking configuration's
`controller_ref`. Its public snapshot carries data only and is never accepted
as admission proof. No public constructor mints the private proof or claim from
strings. The separate stable `host-<enrollment digest>` journal identity remains
a journal identity; the machine record uses the authenticated issuer.

The dependency graph is acyclic:

```text
Host deployment -> machine authority -> typed enrollment proof leaf
Host deployment --------------------> typed enrollment proof leaf
typed enrollment proof leaf -> existing verification/metadata contracts + native IO
Host local root -> Host deployment + existing Host ledger/journal/provider owners
```

The lead approved only this typed admission-capability dependency. Machine
authority does not import Host configuration, local authority policy,
deployment or service modules, and does not duplicate Host policy rules. The
leaf imports no app or Container owner. Signed provider generation is read from
the exact canonical engine policy; actual provider validation and observation
remain the installed machine/provider owners' responsibility.

Enrollment verifies the actual SDK proof and metadata, then opens the one
installed machine writer. The Host retains its cleanup authority before the
fallible `managed_claim_v1` call. Successful admission requires an exact existing
durable charge for the signed ceiling, including the broker partition, before
any observer using deployment-supplied engine policy, deployment publication or
child creation. Fresh empty-WAL genesis is now refused because no real
migration-fence producer exists. Machine opening may observe only its actual
installed provider policy before admission. Every later enrollment publication
rechecks that same existing claim and the signed deadline. Ambiguous failure preserves writer cleanup and durable charge;
neither failure nor close refunds machine capacity.

The completed deployment retains the same claim and a historical recovery
proof borrowing the actual manifest file. Local Host startup, current-owner
checks, reservation, execution refresh, reconciliation, parent budget and
retention use that deployment's claim. The local ledger's allocatable ceiling
equals the signed physical ceiling minus the existing broker partition; it
cannot independently enlarge the machine debit. Native machine, physical host,
service scope and provider identity/generation remain bound across these paths.

Reopen first runs the existing full deployment claim/manifest, credential,
binding and metadata provenance checks without invoking deployment's provider
observer. Only after exact existing machine admission does full provider
observation run. The proof leaf's manifest parser alone
does not validate the full claim/root-child linkage. A recovery-only proof can
match only an existing exact durable reservation; it cannot create a charge.
The stable machine record excludes prepare/recovery timestamps and preserves
the exact policy, enrollment and credential digests. Close retires writer
ownership without changing that record, so reopen observes the same commit.

An empty new machine WAL does not prove that legacy Host workloads are absent.
Fresh-install or migration fencing and adoption of legacy services remain
required and unqualified. Historical recovery cannot create a genesis charge,
but that refusal alone does not establish that a fresh enrollment can coexist
safely with legacy services. The new actual authority gate therefore blocks all
fresh genesis instead of committing a first debit. Exact already-charged replay
remains. This is a safety fix, not completed migration or proof of cross-process
workload absence. See `windows_host_migration_genesis_guard_v1.md`.

Local cleanup closes the Host operation journal first, then the machine claim
writer, then the borrowed native policy/manifest/root owners. Deployment cleanup
retains every actual native policy/manifest handle while machine cleanup is
pending; borrowed proof values own no close operation. No second machine WAL,
writer, runtime export, fabricated grant, wire-selected machine root or local
capacity-release shortcut is introduced.

The two remaining proof scenarios and matching manual live at
`test/03_system/app/orchestrator/feature/windows_managed_host_claim_v1_spec.spl`
and `doc/06_spec/03_system/app/orchestrator/feature/windows_managed_host_claim_v1_spec.md`.
They cover actual signature-first rejection and native borrowed-owner lifetime
when executed. The old positive fresh-enrollment flow is removed and marked
BLOCKED / NOT_COVERED. Genuine pre-existing-charge recovery remains NOT_COVERED
without an actual retained fixture. A separate source regression invokes real
signed enrollment and requires genesis refusal plus the unchanged actual empty
machine WAL. No runtime acceptance is claimed. Per-refresh protected IO, signature checks,
WAL replay and provider observations are intentionally conservative here;
startup/request latency and RSS remain unmeasured, and no performance target
is declared met. Native fault/close retries, execution and crash scenarios
require separate actual Windows evidence.
