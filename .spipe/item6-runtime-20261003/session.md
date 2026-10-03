# Item 6 runtime lane

- Owner/session: `/root/item6_runtime`, `item6-runtime-20261003`
- Worktree: `C:/dev/simple-item6-runtime-20261003`
- Work branch: `work/item6-reader-complete-20261003`
- Target: `refs/heads/release/1.0`
- Base/expected target: `43f626850b6a5531e89110f75cd1eaedc24adcd1`
- Scope: package-index reader acquisition, PSI-REQ-004; prior GC work preserved.
- Owned production file: `src/compiler/80.driver/cache/package_module_index.spl`
- Owned test: `test/01_unit/compiler/cache/package_module_index_reader_transaction_spec.spl`
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

## Reader implementation authorized continuation

The user subsequently requested all code/tests and push despite unavailable
execution. The clean lane switched to `work/item6-reader-complete-20261003` at
release base `43f626850b6a5531e89110f75cd1eaedc24adcd1`. Earlier pending-RED
notes above describe history, not the current implementation state.

Implemented the acquisition algorithm above without changing GC. The private
capture helper returns owned pointer/content/error; the public wrapper always
attempts unlock before checking capture error or hashing/decoding. It returns
`generation-unlock-failed` if the OS unlock fails. The regression additionally
checks independent lock reacquisition after malformed CURRENT and missing
payload failures, then verifies restored publication/readback. No OS-unlock
failure injection primitive exists in this API; that exceptional branch is
reviewed but not directly exercised by a fabricated mock.

Runtime tests remain unexecuted: source implementation is not RED/GREEN or
qualification evidence. Lock contention is bounded by the existing one-second
API and is not a measured successful-read p95. Parent owns integration/push.

## Remote content-integrity continuation

Owner additionally assigned `remote/remote_client.spl` and new
`remote_client_integrity_spec.spl`. Locally owned manifest framing includes all
semantic fields except its claimed digest, with explicit counts/optional marker.
Dependency manifest stays opaque text: no unproven digest-only field contract
is imposed. Ordered reference lists reject duplicates and malformed digest text.
Local SHA256 verifies both manifest and artifact bytes; the transport's legacy
recompute method remains callable for compatibility but is never trusted by
admission. Verified means content integrity, not full graph/provenance authority.

Defensive limits: 4096 artifact/AOP references per list, 1 MiB framed manifest,
64 MiB per artifact and 256 MiB cumulative bytes. Existing manifest/artifact
mismatch results represent malformed/over-budget refusals. Subtraction-based
size admission prevents cumulative overflow and is tested directly at boundaries
without constructing 64 MiB payloads. Transport fetch may already allocate its
response; these are admission limits, not streaming transport allocation limits.

Focused source tests cover valid local-hash admission despite a lying transport,
forged manifest fields/claims, forged artifact bytes/claims, missing data,
namespace/schema/action mismatches, duplicate/malformed references, length
framing, reference boundaries and manifest/byte limits. They remain unexecuted
without an admitted pure-Simple runner. No full-authority or runtime PASS claim.

## Daemon base value ownership continuation

Read-only host review found that free `daemon_base_start`/`stop` functions mutate
a copied struct. Added `DaemonBaseStartV1`, `daemon_base_start_owned` and
`daemon_base_stop_owned` to return updated values explicitly; callers must write
those values back. Legacy wrappers retain their historical caller-state behavior.
Failed acquisition preserves its input state. Stop checks the recorded PID
before the legacy release operation and keeps its receipt if removal fails,
allowing a caller retry; normal stop clears running/acquired state.

Focused filesystem tests cover real PID creation/removal, unchanged original
value, failed repeated/competing acquisition, and foreign-PID replacement.
The legacy PID receipt cannot distinguish later lifetimes of the same PID, and
its compare/delete is not atomic. This API does not replace the host's opaque
exclusive-lock authority. Explicit service facades are not edited in this lane;
the host must directly import the owner module or extend facade exports.
Runtime tests remain unexecuted without an admitted pure-Simple runner.

## Remote acceptance owner adapter

Added `app.test.package_index_acceptance_remote` for canonical scenarios
`remote-cache-local-admission` and `remote-cache-poison-denied`, with actual
local hash observations from `remote_lookup_verified` and an in-memory transport
whose recompute method repeats the untrusted claim. The returned record reports
content verification and exact manifest/artifact digests; it does not report
local semantic/archive admission, graph authority or fabricated filesystem
counters. Three integration cases assert verified bytes, rejected poisoned
bytes and unknown-scenario refusal. Parent/harness owner integrates the record
into main; this lane does not edit main or the cached-binary wrapper.

Read-only review of root `a1a36f44002` confirmed the prior owned-state and stale
request-token P1 findings are closed in source. Wrapper inspection confirmed
missing cached executable produces BLOCKED/exit 2 and no source fallback.
These are static review findings, not runtime qualification.

## Metadata and real source projection adapter

Added `package_index_acceptance_metadata` for clean TLDR admission, demanded
SMF section selection/digest verification, and comment/blank-line source edits.
The source cases call the real parser, frozen module-surface registry, and HIR
closure digest owner; a changed callable signature is a negative control.
No manually toggled header hash is used to claim source-derived equivalence.
Source-only header mutation appears only in the separate narrow cutoff unit
assertion, which does not claim compiler classification.

Fixed two metadata defects: early cutoff omitted compiler-producer and
body-sensitive SMF digest equality; section offset+extent could overflow signed
range validation. Regression cases exercise both and payload out-of-bounds.
The adapter reports metadata decisions and in-memory bytes only, not physical
lazy filesystem read counters or downstream compilation completion.

Generated-source search found opaque `generated_source_digest` fields threaded
through cold HIR drafts and TLDR keys, but no declared-output admission owner in
the inspected compiler/SCV pipeline. Those two adapter scenarios explicitly
return unavailable, not a fake successful declaration check. Implementing the
generator producer/input/output receipt owner remains outstanding. Main harness
is parent-owned. All new Simple tests remain unexecuted.
