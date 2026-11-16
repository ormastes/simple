# Bug-linked workarounds

Status: accepted contract; implementation is pending runtime qualification.
These examples describe the intended interface, not a recorded CLI or SPipe
PASS. Use a qualified self-hosted full CLI that contains the feature.

The user-selected next-rebuild retirement extension is documented in
[workaround_retirement.md](../../05_design/workaround_retirement.md). Its
prepare/admit API is a draft awaiting native qualification and bootstrap
wiring. It requires an applied linked root fix, actual producer/source
admission, and original-form tests in a new isolated checkout. Neither an
existing marker, fetched commit nor a fixed bug status alone authorizes
retirement. Current retained entries are listed in
[the lifecycle inventory](../../08_tracking/bug/workaround_retirement_inventory_2026-10-05.md).

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

## Required workaround traceability

Every temporary build or test workaround must have all three links before it
is used: an immediately preceding `@workaround bug=<canonical-id>` source
annotation, an authoritative bug DB record, and a Git commit containing the
workaround change. This applies to HIR/MIR repairs, temporary test comments,
disabled checks and build-script workarounds. Do not treat a provisional object
or executable as proof that the underlying bug is fixed.

Record the original failure and affected source locations, the recovery commit
for intended code, the workaround commit SHA/link, producer/source identities,
reproducing and prevention tests, and the background fix owner in the bug
record. The workaround commit is distinct from the later underlying-fix commit.
If the qualified DB command is unavailable, retain these fields in a dated bug
report and mark DB reconciliation pending; do not claim the DB was updated.
An unknown defect needs a canonical bug record before a workaround is accepted.

Keep the bug open while the workaround is active. After the underlying fix is
applied and verified with the affected producer, record its commit and narrowly
remove the workaround in a separate linked change. A fetched fix or a changed
DB status alone does not authorize reverting source. Reuse valid caches and
retain original failures throughout recovery.

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


## Closing a bug: `bug-closure-check`, `bug-resolve`, `check-dbs` (verified 2026-11-16)

Verified on the Rust seed `bin/simple.exe` at release tip `75d3cba7d16`, run via
`bin/simple run <entry>` in a scratch git repo with a scratch `bug_db.sdn`
(never the real DB). Against the real 4 MB `bug_db.sdn` the seed printed
`Error: could not load bug database at doc/08_tracking/bug/bug_db.sdn`
(exit 2), so on the real database use the pure-Simple binary.

### `bug-closure-check --id=<id>` (read-only)

Entry `src/app/bug_closure_check/main.spl`. Flags: `--id` (required),
`--disposition=<fixed|closed|triage|duplicate|invalid|wontfix|deferred>`
(default fixed), `--reproducer=<spec>`, `--prevention=<spec>`,
`--rationale=<text>`, `--source-head=<rev>`. Never writes (DB md5 unchanged).
Exit: 0 allowed, 1 blocked, 2 usage / unknown id / DB or git failure.

```text
$ bin/simple bug-closure-check --id=guide_scratch_bug
closure bug=guide_scratch_bug verdict=blocked
  missing reproducer evidence; pass --reproducer=<path>_spec.spl            (exit 1)

$ ... --disposition=wontfix
closure bug=guide_scratch_bug verdict=blocked
  a non-fix disposition needs --rationale=<text>; it is not recorded as a verified fix   (exit 1)

$ ... --disposition=wontfix --rationale="out of scope"
closure bug=guide_scratch_bug disposition=wontfix kind=non_fix_disposition verdict=allowed run_evidence=not_observed head=269fdd12...
  note: workaround index unavailable: workaround index missing; run simple check-dbs --fullscan bugs   (exit 0)

$ ... --reproducer=test/a_spec.spl --prevention=test/b_spec.spl
closure bug=guide_scratch_bug disposition=fixed kind=verified_fix verdict=blocked run_evidence=not_observed head=269fdd12...
  E-BUG-WR-004 proof=workaround_index:incomplete                            (exit 1)

$ ... --id=nope
Error: bug 'nope' not found in database                                     (exit 2)
```

A fix disposition is blocked by E-BUG-WR-004 while the workaround index is
missing or incomplete (build it with `simple check-dbs --fullscan bugs`) or a
live workaround still cites the bug. Outside a git repository it exits 2 with
`workaround Git failed (128)`.

### `bug-resolve` closure flags

`--disposition`, `--rationale`, `--source-head` and `--auto-retire` join the
existing receipt flags (`--date`, `--*-tokens`, `--token-source`,
`--token-provider`, `--knowledge`, `--reproducer`, `--prevention`). The same
gate runs first; a blocked close writes nothing. Labels to keep honest:
- the CLI has no TestDB run source, so every close is `run_evidence=not_observed`:
  it is NOT a test-verified fix;
- a non-fix disposition is logged as `not_a_verified_fix`;
- `--auto-retire` (default off) only LISTS live workaround sites as `path:line`
  after resolving and edits nothing; exit 1 while any remain or the index is
  unavailable.

```text
$ bin/simple bug-resolve --id=guide_scratch_bug --input-tokens=unavailable \
    --output-tokens=unavailable --cache-read-tokens=unavailable \
    --cache-create-tokens=unavailable --token-source=manual --token-provider=manual \
    --knowledge=none --date=2026-11-16 --disposition=wontfix --rationale="out of scope" --auto-retire
Resolved bug guide_scratch_bug (status: Closed, updated_at: 2026-11-16)
auto-retire: guide_scratch_bug: workaround index unavailable (workaround index missing; run simple check-dbs --fullscan bugs)
(exit 1)
```

### `check-dbs bugs`: `closure_gate_bypass`

`simple check-dbs bugs [--fullscan]` (`src/app/cli/check_dbs.spl:68`) emits a
warning-severity issue `closure_gate_bypass` (E-BUG-WR-004) for a bug already
marked fixed or closed that still has a live workaround, i.e. it was closed
outside the gate. Advisory only: it reopens nothing. Not demonstrated with real
output here (it needs an indexed workaround for a closed bug); the source line
above is the evidence.
