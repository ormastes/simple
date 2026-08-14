# SOSIX QEMU remaining-owner system-test plan

Executable spec:
`test/03_system/os/qemu/sosix_qemu_remaining_owners_spec.spl`.

## Oracle

The spec uses bounded process capture and typed `CommandEvidence` and
`RowOracle` values. The retained handoff oracle contains exactly 24 stable IDs
and expects 3 `PASS`, 15 `BLOCKED`, and 6 `POSTPONED`. The three Linux
lifecycle sources now also have direct-QEMU implementation receipts, but remain
non-PASS here until the self-hosted SSpec/docgen and canonical producer bundles
run. A non-PASS expected state proves
only honest retention in this handoff test; it cannot promote a live row.

## Frozen displayed steps

1. `Validate matrix promotion`
2. `Reject mutable source aliasing`
3. `Bind the admitted runtime`
4. `Admit the Linux guest lifecycle`
5. `Record unavailable native hosts`
6. `Retain the implementation handoff`

## Exact verification commands

After a source-matched admitted full CLI exists, run once:

```sh
release/x86_64-unknown-linux-gnu/simple test test/03_system/os/qemu/sosix_qemu_remaining_owners_spec.spl --mode=interpreter
release/x86_64-unknown-linux-gnu/simple spipe-docgen test/03_system/os/qemu/sosix_qemu_remaining_owners_spec.spl --output doc/06_spec --no-index
```

The test must pass and docgen must report zero stubs. Exit 139, timeout,
missing output, or a handwritten manual is FAIL/BLOCKED, never substitute
evidence.

## Current implementation evidence

- RV64: Sv39-isolated U-mode, checked ELF/FAT admission, exact fault provenance,
  supervisor-state restoration, generation-bound exact-once reap, and live
  `TEST PASSED` are implemented and directly exercised.
- x86_32: PAE/NX-isolated CPL3, checked ELF/FAT admission, context round trip,
  exact #GP/#PF ownership, generation-bound reap, and live `TEST PASSED` are
  implemented and directly exercised.
- ARM32: EL0 page isolation/W^X, checked ELF/FAT admission, authenticated fault
  and SVC ownership, scrubbed first-entry registers, exact reap, and live
  `TEST PASSED` are implemented and directly exercised.

These receipts close the source/lifecycle implementation blockers in AC-4
through AC-6. They do not promote a matrix row without a source-matched admitted
runtime, canonical producer bundle, executable SSpec, and generated manual.

The current bootstrap continuation also completes the typed parser-contract
owner and proves Stage 2 plus its sanity gate. Stage 3 selects the transient
per-file module-surface owner, and its provenance hash and actual launch bind
that selection. This lane constructs compact surfaces before pausing the
transient scope, retains compact function headers through desugaring, and
splits the former 60 KiB interpreter source into three physical parser units.
The final bounded run nevertheless released the same first ten surfaces, then
grew from about 4.4 GiB to 8.7 GiB while processing the next closure source and
before an eleventh release receipt. It was terminated before host OOM. Because
the admitted Stage 2 executes its previously compiled release-only telemetry,
the new parse/build/promote substage receipts cannot become observable until a
Stage 3 artifact exists; the remaining owner is therefore honestly bounded to
the Stage-2 compiler's processing of physical source 11, not yet to one of
those substages. A proposed planner receipt producer was rejected in highest-
capability review because its shell transcript was self-asserted and forgeable;
canonical planner admission therefore remains fail-closed. The three-cycle cap
is exhausted. No Stage 4 CLI was deployed,
so the exact SSpec/docgen commands above remain pending and must not be run
against the known-stale release binary.
