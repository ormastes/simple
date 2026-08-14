# SOSIX QEMU remaining-owner system-test plan

Executable spec:
`test/03_system/os/qemu/sosix_qemu_remaining_owners_spec.spl`.

## Oracle

The spec uses bounded process capture and typed `CommandEvidence` and
`RowOracle` values. The row oracle contains exactly 24 stable IDs and expects
3 `PASS`, 15 `BLOCKED`, and 6 `POSTPONED`. A non-PASS expected state proves
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
