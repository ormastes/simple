# macOS Full-CLI GUI Admission Process Proof

**Status:** source fixed / review accepted / live Endpoint Security evidence unavailable (exit 125)
**Evidence row:** `MAC-WM-GLASS-LOCAL-001`

The manifest-v3 source boundary has been repaired and independently accepted:

1. The canonical `build/bootstrap/full/<platform>/simple` root is classified
   by exact admitted executable identity and role, not a path substring.
2. The polling/self-attested receipt was replaced by a normalized v2 history
   verifier plus a fail-closed trust-root gate. The verifier requires a
   finalized, gap-free execution history
   beginning with the exact root PID/path; checks fork/exec/exit ordering,
   parent identity, live-state transitions, complete descendant exits, and
   root-last exit; and rejects forbidden-role same-PID delegation, short-lived
   forbidden descendants, or policy/collector/provenance/signing drift.
3. Admission accepts only the tracked collector source and policy identity.
   Arbitrary collector paths or caller-authored receipts cannot cross the
   production boundary.

The source repair is committed and accepted. It intentionally remains
fail-closed with exit 125 because the checked-in Swift collector and the
`status=admitted` trust-root branch are deliberate placeholders, and this host
also has no provisioned signing team, Endpoint Security entitlement, signed
provenance-bound collector, or source-matched canonical full-CLI GUI artifact.
This is unavailable live implementation/provisioning, not rejection of the
accepted verifier and fail-closed boundary.

## Prepared-host completion

Implement and independently review the real Endpoint Security exec/fork/exit
collector, reproducible collector-build provenance, and the admitted
policy/team/entitlement authentication branch. Update the pinned policy
hashes/status to those reviewed artifacts. Then provision an approved macOS
signing team and Endpoint Security entitlement, build/sign the collector with
those identities, bind its provenance to the canonical full-CLI producer, and
produce the source-matched GUI driver and manifest. Finally run these exact
focused contracts:

```sh
sh test/01_unit/scripts/macos_gui_execution_history_boundary_contract.shs
sh test/01_unit/scripts/macos_gui_full_cli_provenance_contract.shs
sh test/01_unit/scripts/macos_gpu_trusted_build_admission_contract.shs
```

Do not bootstrap or substitute the Rust seed. After the contracts pass against
the provisioned identities and artifact, run:

```sh
sh scripts/check/check-macos-vulkan-gui-widget-live-evidence.shs
sh scripts/check/check-macos-vulkan-web-live-evidence.shs
```
