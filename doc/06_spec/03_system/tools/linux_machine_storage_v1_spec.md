# Actual installed Linux machine storage v1

**AUTHORED_NOT_RUN — authored manual, not generated SPipe evidence.**

Source: `test/03_system/tools/linux_machine_storage_v1_spec.spl`.
Requirements: REQ-LINUX-MACHINE-STORAGE-001 through 003.

An administrator prepares a disposable Linux x86_64/aarch64 fixture with the
fixed root-owned policy and the dedicated service UID's private delegated
state/WAL directories described in `doc/05_design/linux_machine_storage_v1.md`.
Run as that nonroot UID on its actual process leader thread. The fixture does
not install policy, elevate, launch Podman or use a seed runtime. Binding can
persist, so this scenario must not target a live ledger.

1. **Read actual administrator policy and current native process identity.**
   Open the zero-argument installed policy factory. Assert actual real and
   effective UIDs agree and are positive, thread/process IDs agree, the native
   principal is `linux:uid:<actual UID>`, and both diagnostic digests have the
   expected SHA-256 length. Decode the actual protected policy and require the
   installed Linux provider's UID pin to equal the actual process context.
2. **Transfer the reader into the fixed delegated state and retain its sole
   writer.** Transfer once, then assert reader aliases cannot read or produce
   current principal context and cannot close the storage's backing owners.
   Bind the actual bytes and require its exact SHA-256 digest. Altering those
   bytes must fail binding. Observe positive native CPU/memory totals and the
   actual current WAL head.
3. **Reject a competing actual writer and close all of its returned owners.**
   Open a second actual installed reader and attempt transfer while the first
   writer is live. Require rejection or cleanup, never Ready; close the exact
   returned owner and require successful release. Failed helper acquisitions
   retain their owners before reporting failure.
4. **Refuse a new charge without the actual migration fence and preserve the
   current head.** Submit a concrete WAL record with an empty expected parent.
   Require `machine-container-migration-fence-unavailable` and the same current
   head afterward. Empty state is not proof that previous charges disappeared.
5. **Consume the exact native owners once and reject all closed aliases.**
   Close the storage, require native release, reject a later WAL observation,
   and require stale results from both closed aliases. Close error and unknown
   release outcomes are failures in this positive fixture, not passing cleanup.
6. **Reopen after every capsule closes while keeping the same process-lifetime
   origin.** Open a fresh actual reader, require the same native process digest
   and a later owner generation, and close it. This exercises the persistent
   origin's lifetime; it does not qualify the separate nested-PID fork fault.

No runtime or native checks have been executed. Unsafe ancestry, foreign map
bind mounts, changed namespaces, inherited owners, unknown release and numeric
descriptor reuse require separate native fixtures; they are not covered by a
source scan or claimed PASS here.
