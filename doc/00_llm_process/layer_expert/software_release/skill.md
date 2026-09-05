# Software Release Layer Expert

The software-release layer converts canonical version, VCS policy, session, backport/forward-port convergence, candidate, admission, and artifact facts into fail-closed plans before provider mutation. Its scheduled main/release discovery is read-only; exact reviewed changes cross protected lines only through isolated sessions, renewed evidence, divergence receipts, and integration-authority CAS. `main` remains the independent development trunk.

Canonical references:

- `doc/07_guide/infra/software_release.md`
- `doc/04_architecture/release_process_hardening.md`
- `release/version.sdn`
- `.spipe/policy/vcs.sdn`
- `src/app/release/policy.spl`

Protected mutation belongs to the lifecycle/integration gateway; compiler admission belongs to bootstrap owners. This layer must not duplicate either boundary or add raw Git/process/runtime shortcuts.

Review admission prefers a closed, exact-head high-capability/high-effort model
receipt. The sole-owner fallback is explicit, expiring, audit-bound, and allowed
only for verifier unavailability with reason `no eligible independent reviewer`.
Only a pinned dedicated verifier/broker GitHub App may project the admission
status or custom environment protection; missing App IDs block live apply.
