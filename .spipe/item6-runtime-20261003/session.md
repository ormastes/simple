# Item 6 runtime lane

- Owner/session: `/root/item6_runtime`, `item6-runtime-20261003`
- Worktree: `C:/dev/simple-item6-runtime-20261003`
- Work branch: `work/item6-runtime-20261003`
- Target: `refs/heads/release/1.0`
- Base/expected target: `7d16ab11d2227cbe5f29dc998b76a1eff326abbb`
- Scope: package-index GC/publication mutual exclusion, PSI-REQ-004.
- Owned production file: `src/compiler/80.driver/cache/package_module_index.spl`
- Owned test: `test/01_unit/compiler/cache/package_module_index_gc_publication_spec.spl`
- Integration owner/reviewer: parent `/root`; no lane pushes or PRs.
- Initial status: tracked worktree clean; LFS checkout reported historical non-pointer blobs but no tracked changes.
- Runner admission: unavailable. `C:/dev/simple/bin/release` absent. Root `bin/simple.exe` SHA256 `E2A42543D62F794A8DF8389DE70C4200FF95675B5C48B60F0103B1F47A77E78C` has no established self-hosted receipt; not executed. `bin/simple.cmd` can fall back to Rust and is not permitted.
- RED/GREEN status: unexecuted; runtime behavior must be verified before qualification.

## Evidence and next command

The baseline GC reads CURRENT once without the publication lock. A publisher
can promote B after GC observed A; GC then deletes B and leaves CURRENT dangling.
The regression holds the same OS lock through a distinct handle and checks
zero removals plus exact current/candidate/pointer bytes, retained-generation
preservation, and successful post-unlock reclamation. The initial test existed
before implementation (SHA256 `470695E16DA77942FB339C970A85ED499DEC26E03FFF9A42E958B8F5A1F498AD`);
the retained-generation assertion was added afterward. This is test-first
source work, **not executed RED/GREEN evidence**.

`file_lock` positive timeout is bounded on Windows LockFileEx and Unix flock;
nonpositive timeout blocks indefinitely. GC now uses one second and delegates
all early returns to an internal helper so the wrapper always unlocks. Zero
continues to mean no removals and now also covers contention; public API unchanged.

An adjacent bootstrap's `stage2-runtime-authority/simple.exe` is not admitted
as a pure-Simple test runner. Its bootstrap-progress log terminates
`VERDICT — ABORTED: stage=stage2 exit=1`, and its linker log reports undefined
`rt_fd_stat_snapshot_v1`. No adjacent artifact was executed or modified.

Once an immutable admitted pure-Simple runner is available, execute baseline
with this test to collect RED, then this branch for GREEN, using:
`<runtime> test test/01_unit/compiler/cache/package_module_index_gc_publication_spec.spl --mode=interpreter`.
Record actual runner hash, compiler lineage, source commit, stdout, exit, and
assertion counts. Compiler/lib/MCP/LSP smoke gates remain the parent integration
owner’s required qualification; no release or completion is claimed here.

## Unclosed reader acquisition requirement

This fix closes only writer/GC exclusion. `package_module_index_read_current_v1`
still reads CURRENT and then its payload without atomic reader pin acquisition.
The caller-supplied retained-digest list cannot protect an unregistered reader
paused between those reads. Future acceptance must pause a reader after
observing A, publish B, collect while that reader still owns A, then resume it
and verify A's exact payload remains readable until its pin is released.
No full atomic lifecycle or reader/GC safety claim is supported by this change.

## Reader contract continuation

The eight production consumer files read fully owned decoded values/digests;
none retains an index path or lazily rereads index bytes. Thus the requirement
above can be met for index records without a persistent reader-pin registry:

1. Preserve absent CURRENT/storage as `missing-or-invalid-generation`, without
   creating its directory.
2. Acquire the same CURRENT.lock; one second is the smallest bounded timeout
   supported by existing file_lock. Refusal is `generation-lock-unavailable`.
3. While locked, validate CURRENT and read exact bounded generation bytes into
   owned memory. A private helper returns pointer/content/error to one unlock
   owner, including all early error paths.
4. Unlock before SHA256, decode, or any caller logic. Authenticate captured bytes
   against captured pointer, then return the fully owned decoded generation.

No publisher/GC locked helper calls public read_current, so this does not add
recursive locking. The archive loader returns CAS paths independently; the
index collector removes only `.index` files, not those archive paths. Separate
archive lifetime work remains outside this index-record repair. One-second
contention is diagnostic behavior, not demonstrated hot-path latency compliance.

The new `package_module_index_reader_transaction_spec.spl` contains three real
contracts: held-lock rejection and post-release success, decoded value survival
after its backing index file is collected, and absent-root compatibility.
Production reader remains unchanged pending an actual executed RED per parent
instruction. No RED/GREEN or test pass is claimed. The adjacent bootstrap
recheck still reported stage2 ABORTED; root `bin/release` remained absent.
