# Bug-linked workarounds

Status: accepted contract; implementation is pending runtime qualification.
These examples describe the intended interface, not a recorded CLI or SPipe
PASS. Use a qualified self-hosted full CLI that contains the feature.

## Mark the affected block

Place a comment immediately before the source block that temporarily avoids a
known defect:

```text
# @workaround bug=<canonical-id> [recover=<7..64hex>] [reason=<text>]
```

Replace the placeholders; brackets mean optional fields, not literal syntax.
Use the canonical ID of an existing bug record. `//` is also accepted as the
comment prefix. The optional `recover` field is a Git recovery reference of
7–64 hexadecimal characters. Put the optional reason last and describe the
defect being avoided. The marker does not resolve the bug or waive a failed check.

## Find related workarounds

```sh
simple check-dbs bugs
simple check-dbs bugs --bug=<canonical-id>
simple check-dbs --fullscan bugs
```

Ordinary bug checks read the derived `.simple/workarounds.sdn` index and join
its links to the authoritative bug database. They do not scan source or repair
the index. Open bugs show linked locations; fixed or closed bugs with remaining
links need recovery review. Unknown bug IDs are reported.

A missing index, invalid metadata, or HEAD mismatch cannot establish current
coverage. Run explicit fullscan to reconcile tracked and nonignored untracked source paths. An empty
indexed result does not prove the source tree is clear when coverage is
incomplete. Fullscan collects both kinds with one bounded Git invocation.
Read-only queries explicitly say that current checkout freshness is unchecked:
the stored `complete` flag describes coverage at the recorded refresh revision,
not live branch state. A build detects a changed HEAD and marks coverage incomplete;
queries do not run Git to discover a branch switch themselves.

The parent `native-build` invocation discovers changed/untracked candidates
plus previously linked paths once. It reparses current contents, removes links
for deleted files or removed/reverted annotations, and publishes one validated
transaction. Workers never update the index. A malformed batch preserves the
last valid index and reports failure; that retained snapshot is not successful
refresh evidence. Do not hand-edit this derived database.

Operation budget per parent refresh: two `rev-parse` calls and at most one
changed-path Git collection (each has a 30-second deadline and 16 MiB output
bound); one lock wait of at most five seconds; at most one 8 MiB bounded read
per changed/untracked or previously linked candidate; one canonical bug DB read
of at most 32 MiB only when the batch contains markers; one index payload of at
most 16 MiB; at most one atomic publication, skipped when unchanged. Known
changed-path callers omit Git status discovery. These are operation and safety
bounds, not latency results. Warm query and refresh time, Git time, candidate
counts, bytes read, and actual publication counts still need measurement on
an admitted runtime before a performance claim or release acceptance.

## Recover intended source

1. Fix the compiler, library, or runtime owner of the bug and run the focused
   regression that proves the relevant defect is fixed.
2. Query that bug's indexed links. Resolve incomplete coverage before claiming
   all linked blocks have been reviewed.
3. Compare each current block with its optional historical recovery reference.
   The hash is review evidence only: it never authorizes automatic checkout,
   reset, or whole-file restoration.
4. Restore only the intended block after reviewing surrounding changes and
   other active work. Remove the obsolete annotation. Record any related block
   that still needs a workaround.
5. Let the next parent build refresh the links. Build the smallest affected
   entry or dependency scope whose cache owner can prove valid, then complete
   the required verification boundary.

Keep producer, entry, dependency, ABI, and build-option identities intact.
Preserve compatible caches and failed-attempt evidence; never rewrite stamps
to force reuse. If invalidation is necessary, name the incompatible input and
invalidate only the supported affected scope. Defer the one final clean gate
to the required bootstrap/release boundary after focused repairs pass; a
workaround edit alone is not a reason to restart every phase.

## Overlap bootstrap diagnostics

On Windows and Linux, an available compiler binary allows dependent Phase 3
diagnostic work to start while Phase 2 admission continues. Start Phase 4
diagnostics as soon as its required compiler binary exists. Record exact
producer bytes, source identity, commands, and outcomes; isolate each writable
cache and output. Share available CPU capacity across independent lanes within
memory limits. Binary existence establishes readiness to try the next build,
not admission or correctness. Keep diagnostic results provisional and require
normal admission, lineage, and verification gates before promotion.

See [cache policy](bootstrap_cache_policy.md),
[scheduler contract](bootstrap_speculative_scheduler.md), and
[accepted requirements](../../02_requirements/feature/bug_linked_workarounds.md).
