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
peer has a source-present producer-backed x86_64 `-Run` path; the other five
descriptors fail closed until their guest kernels echo the distinct collector
nonce. Only native Windows execution can verify a path or create row evidence.

The L0 collector/media/runtime repairs are implemented in source. Do not call
L0 verified until the bounded typed SSpec passes on a source-matched admitted
full CLI and `spipe-docgen` produces a zero-stub manual. The SSpec's expected
3 PASS / 15 BLOCKED / 6 POSTPONED oracle proves honest handoff state, not live
matrix completion.

Collector v2 now byte-binds the exact 13-field admission record in the
manifest, and the pure-Simple trusted importer exposes only the closed-root
all-24-PASS release predicate. Its new focused sabotage specs remain unexecuted
without an admitted Stage-4 CLI; pre/post path/hash checks do not claim
fd-pinned protection against hostile concurrent replacement.

## Update rule

Refresh this expert, the plan, ledger, and guide together whenever a row state,
shared interface, resume command, ownership boundary, or promotion rule changes.
