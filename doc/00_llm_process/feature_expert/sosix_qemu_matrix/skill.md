# Feature Expert: SOSIX QEMU Filesystem Matrix

## Source of truth

- Plan: [`sosix_parallel_qemu_refactor.md`](../../../03_plan/agent_tasks/sosix_parallel_qemu_refactor.md)
- Evidence ledger: [`sosix_qemu_matrix_evidence_status_2026-08-13.md`](../../../03_plan/sys_test/sosix_qemu_matrix_evidence_status_2026-08-13.md)
- Operator guide: [`sosix_qemu_shared_settings.md`](../../../07_guide/platform/simpleos/sosix_qemu_shared_settings.md)
- Open owners: [`sosix_qemu_matrix_remaining_owners_2026-08-14.md`](../../../08_tracking/bug/sosix_qemu_matrix_remaining_owners_2026-08-14.md)

## Contract

The matrix is four hosts by six guests. Every row has a stable
`SOSIX-<HOST>-<GUEST>` acceptance ID. A PASS requires admitted native-host
identity, immutable base media plus a row-owned nonce copy, ordered guest entry,
real `/SYS/APPS` listing, mounted program stdout, exit 37, exact reap, and a
producer-generated bundle. The parent collector alone may promote exactly 24
rows. Blocked/postponed rows stay active and are never exclusions or PASS.

The manual flow and shared script names are frozen in the plan. Producer
`--self-test` proves fixture closure only. Windows preflight, TCG correctness,
cached transcripts, and host-side execution are not row evidence. The Windows
peer has six distinct bounded collector-nonce readers. Only x86_64 and ARM32
currently have the complete workload/listing/program/reap source contract;
the other four descriptors must fail before ready. Source gates are not
execution evidence; only native Windows execution can create row evidence.

The L0 collector/media/runtime repairs are implemented in source. Do not call
L0 verified until the bounded typed SSpec passes on a source-matched admitted
full CLI and `spipe-docgen` produces a zero-stub manual. The SSpec's expected
3 PASS / 15 BLOCKED / 6 POSTPONED oracle proves honest handoff state, not live
matrix completion.

Collector v2 now byte-binds the exact 13-field admission record in the
manifest, and the pure-Simple trusted importer exposes only the closed-root
all-24-PASS release predicate. Its multiline boolean forms use the required
parenthesized Simple grammar. Both focused specs and a module check were
attempted once with the deployed self-hosted CLI but exited 139 before usable
results, so they remain unverified without an admitted Stage-4 CLI. Pre/post path/hash checks do not claim
fd-pinned protection against hostile concurrent replacement.

## Update rule

Refresh this expert, the plan, ledger, and guide together whenever a row state,
shared interface, resume command, ownership boundary, or promotion rule changes.
