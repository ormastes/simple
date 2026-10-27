# Build retention store admission and eviction

Source: `test/02_integration/app/scv_build_retention_store_v1_spec.spl`.

Execution status: **NOT_RUN**. These scenarios are authored; SDN parsing,
filesystem callbacks and OS lock behavior have not executed on an admitted
general Simple runtime. This companion was reviewed manually.

1. Publish a valid authority root, derive an eviction plan, and execute it.
   The existing snapshot store verifies provenance and receipt, removes the
   snapshot unit, and persists the new graph generation.
2. Plan deletion, then pin the snapshot through generation CAS. Execution of
   the earlier plan fails; the legacy collector also preserves the snapshot.
3. Hold the shared OS lock. Admission times out and fails closed. Release it,
   corrupt durable SDN, and confirm loading and legacy deletion refuse it.
4. Leave an old lock file with no OS owner. Admission succeeds using the same
   stable inode. The file remains present after release, preventing inode split.
5. Tamper with a same-generation plan or attempt replacement that drops
   authoritative history. Both are rejected before touching snapshot bytes.

Parent integration initializes an empty durable authority before managed
snapshot acquisition, then appends immutable objects and publishes their pins
or reader leases by CAS. All admissions and deletions use the same OS-owned
`flock`/`LockFileEx` facade with a finite one-second contention timeout. The OS
releases ownership after process exit; implementations never unlink the lock
file. A reader's expiry timestamp is advisory until explicit release.

Each deletion rechecks the durable canonical root and generation while holding
the lock, issues a single exact permit, and calls the existing store owner.
The physical callback rereads that authority immediately before removal.
Legacy GC and cleanup also acquire the shared lock, then refuse managed roots.

Physical eviction supports only `snapshot` units, including their provenance
receipt. Other namespaces remain part of graph protection and fail explicitly
when no checked store callback exists. A crash between physical removal and
authority rewrite may leave an incomplete transaction requiring recovery; this
is not an atomic multi-object deletion or power-loss qualification. A missing
or corrupt object is never reported as successfully deleted. Real process-kill
and power-loss execution remain required before claiming crash qualification.
