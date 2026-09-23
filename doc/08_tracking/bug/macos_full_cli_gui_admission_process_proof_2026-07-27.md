# macOS Full-CLI GUI Admission Process Proof
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** open — post-spawn rejection cleanup fixed and Astra reviewed; collector source contract PASS; live Endpoint Security admission unavailable (no approved signing identity)
**Evidence row:** `MAC-WM-GLASS-LOCAL-001`

The cycle-3 source candidate repairs the previously rejected boundary:

1. The canonical `build/bootstrap/full/<platform>/simple` root is classified
   by exact admitted executable identity and role, not a path substring.
2. The EndpointSecurity handler now rejects missing `seq_num` /
   `global_seq_num` support and sequence gaps, clears and validates process/path
   muting, bounds pre-root pressure, retains only exact root lineage, and waits
   on a bounded finalization barrier after the root wait. The normalized v3
   verifier binds original-driver provenance to the immutable private snapshot
   actually executed and rejects incomplete descendant/root exit history.
3. Admission accepts only the tracked collector source and policy identity.
   Arbitrary collector paths or caller-authored receipts cannot cross the
   production boundary.
4. Collector construction and admission are separate. A tracked `prepared`
   policy pins source, build, entitlement, signing identity, compiler, SDK,
   target, exact argv, and deterministic environment before candidate build.
   Only a later reviewed tracked `admitted` update may pin candidate output and
   manifest hashes. The manifest binds a non-circular candidate-policy digest
   and never hashes the final policy that pins it.
5. The builder first authenticates tracked policy and builder bytes, re-execs
   an immutable private builder copy, and uses mode-0400/0500 private snapshots
   for source, entitlement, candidate, manifest, and admission checks. Mutable
   repository/build pathnames are provenance labels only after snapshot.
   Compiler, codesign, SDK, and SDK settings must be canonical root-owned,
   parent-chain non-writable paths; executable tools must retain Apple code
   signatures and the caller must not be root. Full-CLI execution goes through
   `--exec-verified`, which execs the exact immutable admitted collector
   snapshot rather than returning to a mutable collector pathname.

Historical cycle-3 state (superseded for the collector gates by the 2026-09-22
entry below): The candidate is not accepted until its focused gates and independent review
pass. The builder `--self-test` reached its immutable-manifest restore fixture,
but was not rerun after the final mode-0400-to-0600 fixture repair. Swift source
typechecking reached the link step, but the compile/link self-test cap was
exhausted before the final SDK-confirmed `-lbsm` link correction could be
rerun. These are two distinct, exact unrerun gates. The tracked policy remains
`status=unavailable` with unassigned signing and toolchain identity and
therefore exits 125; no live, source-level, link-verified, shell-gate, guard, or
review-accepted PASS is claimed.

## Prepared-host completion

Provision an approved macOS signing team and Endpoint Security entitlement.
First commit a reviewed `status=prepared` policy with every source/toolchain
pin, then run
`sh scripts/check/build-macos-es-history-collector.shs --build-candidate`.
Review the candidate, commit a separate `status=admitted` policy update with
its output and manifest hashes, and run the wrapper's `--verify` admission.
Then bind that admitted provenance to the canonical full-CLI producer. Finally
run these exact focused contracts:

```sh
sh test/01_unit/scripts/macos_gui_execution_history_boundary_contract.shs
sh test/01_unit/scripts/macos_gui_full_cli_provenance_contract.shs
sh test/01_unit/scripts/macos_gpu_trusted_build_admission_contract.shs
sh test/01_unit/scripts/macos_es_history_collector_contract.shs
```

Do not bootstrap or substitute the Rust seed. After the contracts pass against
the provisioned identities and artifact, run:

```sh
sh scripts/check/check-macos-vulkan-gui-widget-live-evidence.shs
sh scripts/check/check-macos-vulkan-web-live-evidence.shs
```

## 2026-09-22 — post-spawn rejection cleanup

Source review found a separate child-lifecycle bug: after successful spawn,
process-group validation or `bindRoot()` rejection could return without
terminating and reaping the owned child. The candidate now retains explicit
ownership until reap, terminates only the unreaped child/its anchored group
on rejection, and makes cleanup idempotent after normal wait. Real-process
Swift self-tests cover pre-root failure, actual process-group mismatch,
sibling survival, reaping, and the successful-wait path. A missing-scope-cleanup
mutation is rejected by the new test. See
`doc/09_report/macos_es_negative_admission_2026-09-22.md` for the bounded run
and resource evidence. Independent Astra review approved corrected source
`d5922bf44e1`; the canonical collector source contract then passed against
that clean commit in 23.15 seconds (sampled process-tree peak 208,064 KiB
under the enforced 5,859,375 KiB cap). This source fix does not supply the
missing Apple identity/entitlement; the canonical bug remains open.
