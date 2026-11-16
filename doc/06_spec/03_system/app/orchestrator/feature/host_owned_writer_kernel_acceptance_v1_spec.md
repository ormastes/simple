# Actual private writer kernel acceptance subset

AUTHORED_NOT_RUN. Three registered modern SSpec scenarios with a hand-written
manual; no compiler, native, spec or docgen execution and no observed pass. Source:
`test/03_system/app/orchestrator/feature/host_owned_writer_kernel_acceptance_v1_spec.spl`.

Supports ONLY the writer-serialization subset of AT-HOST-02/05. It does not prove
memory reservation, exclusive GPU, cross-user Host identity, signed grants,
installed service, engine behavior, transport faults or any full acceptance row.

## Real setup and bounded cleanup

An actual Linux native runtime must support `secure_temp_dir` and generation-owned
file-lock acquisition/release. The fixture creates real private directories and
obtains every owner exclusively from `file_lock_open_owned_v2`; no token/FD/PID,
owner DTO or Boolean grant is manufactured. Missing native prerequisites fail,
not skip. Other platforms do not yield a fake Linux pass.

The three approved helpers are `acceptance_owned_writer_begin_v1()->Result<(),text>`,
`acceptance_owned_writer_expect_blocked_v1(path:text)->Result<(),text>` and
`acceptance_owned_writer_finish_v1()->Result<(),text>`. Suite-local fields retain
one fixture's actual owners/paths, not a capability lookup registry. Every Ready,
CleanupRequired or release turn is adopted before errors/assertions. Unexpected
successful contenders remain owned until actual cleanup. A failed cleanup sets a
sticky diagnostic, retains returned owners and private paths, and forbids further
open/delete/retry. Directory deletion occurs only after positive closed/no-owner
release of all current owners. No sleeps, process kills or unbounded retries.

## should keep the replacement kernel lease held after an old generation release

1. Open a genuine private writer lease.
2. Rotate the exact native generation: release A, adopt its result, acquire B at
   the same private path; retain B before checking acquisition outcomes.
3. Release the copied A token and require an owner-free stale refusal.
4. Probe kernel contention after stale release: a NEW actual competing acquire
   must be rejected while B remains held. This goes beyond the existing
   engine_exec_owner_v3 test's cached `held` state query.
5. Close the exact returned cleanup owners; do not retry raw integers.

## should preserve an unrelated private writer while another root is released

1. Open a genuine private writer lease.
2. Create a distinct actual private directory with the same fixed lock leaf;
   acquire its independent genuine owner.
3. Preserve unrelated private writer custody: release the first root's owner,
   then require actual contention at the second root and its held generation.
4. Close the exact returned cleanup owners before deleting either private root.

This is private-file scope separation, NOT two-rootless-user physical GPU proof.

## should refuse invalid acquisition metadata without releasing the current writer

2. Reject an invalid acquisition timeout while the current writer stays held:
   invoke the real public acquisition API with a negative timeout.
3. Require the actual configuration refusal, then independently attempt a valid
   competing acquire to prove the current kernel lease remains held.
4. Close the exact returned cleanup owners. Unexpected Ready/CleanupRequired
   is retained and fails the case rather than being discarded by an assertion.

Dependency pin (git blob ids, identical at release 4934dd32445 and at
origin/release/1.0.0 9688ab99d83): `src/lib/nogc_sync_mut/io/file_lock_owned_v2.spl`
d342a4e5b6, `src/lib/nogc_sync_mut/io/file_ops.spl` da9b2fd868,
`src/lib/nogc_sync_mut/io_runtime.spl` 23bb40e104. The root-level
`src/lib/io_runtime.spl` is a distinct file and is not substituted. No runtime
qualification was performed: no `simple` binary was available, so the scenarios
are NOT_RUN. The full 11-row Host/container matrix remains unqualified.
