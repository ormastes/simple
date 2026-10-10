# Item 7 release synchronization and bootstrap gate

Status: locally rebased; bootstrap admission refused; not pushed.

The preserved `work/item7-completion-20261003` branch at
`117a32274faa96b183d603992e08b40e54f9b294` was recovered into the isolated
`C:/dev/simple-item7-sync-20261009` worktree on `work/item7-sync-20261009`.
Its commits were rebased onto fetched `release/1.0` at
`c81c8080039215961747b86d481278080d75b375`. Rebased implementation head:
`d876cb6795f`. The old branch and unrelated dirty main worktree were preserved.

Conflicting additive imports were combined. Already-landed watchdog changes
were not reapplied over newer release/FreeBSD behavior. Read-only review of
seven overlapping compiler files confirmed preservation of retained-owner HIR
checks, K1 callbacks, canonical object paths, BFD probing, diagnostic retention,
newunit resets, codec reader construction, lock imports, and semantic policy.
The rebased tree has 142579 tracked files versus release's 142547: 32 additions,
61 modifications, zero deletions. The full release-to-head whitespace check passed.
These are source/integration checks, not runtime verification.

## Actual bootstrap check

Executed from the rebased worktree with an isolated storage root and a 30-second
bound:

```sh
SIMPLE_WORKTREE_STORAGE_ROOT=/c/dev/simple-item7-sync-20261009/build/item7-bootstrap-check \
timeout --kill-after=3s 30s sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --validate-bootstrap-receipt
```

Exit **64**: `bootstrap-policy-error: reason-receipt-required`.
Logs: `build/item7-sync-evidence-20261009/bootstrap-admission.log` and
`bootstrap-admission.exit`. No build stage started. A preliminary scripts-only
archive check lacked the kernel policy manifest and was not considered evidence
of a bootstrap regression; the complete-worktree refusal above is authoritative.

The newer Windows producer under `build/rc1-newp2-hello40-preparation/producer`
remains diagnostic-only: its qualification failed outer process-owner cleanup.
Other sessions' successor and item3 builds were left untouched. No admitted full
CLI was discovered. Before pushing as stable, obtain a canonical planner receipt
bound to an admitted parent, runtime snapshot, planner and current source, then
run bootstrap and the pending compiler acceptance checks. Do not fabricate
authority or substitute diagnostic binaries. Full item 7 coding, runtime
verification, and the mutable-link-input receipt repair remain incomplete.


## 2026-10-10: latest release and bounded Phase 2 diagnostics

STATUS: FAIL for release readiness. No feature push or merge performed.

Rebased all 39 retained commits onto fetched `release/1.0`
`f92764f2b97f99de8b60db2d454208de55564be2`. The rebased head was
`2b536680aac`; integration repairs were checkpointed at `741f4c5d8a2`.
Preserved release binding inference, typed pool promotion, native trait imports,
and runtime value tracking alongside the collection implementation.
The release and feature branches both independently used flat-pool v3 for
incompatible additions: their combined layout is now v4. Cache fixtures follow
that version. Named-argument graph validation now traverses function parameters
and return tags; valid and corrupt-cache regression cases were added but have
NOT executed. A smaller-model agent performed bounded reviews/implementation;
the parent reviewed its diffs. The unrelated dirty main worktree was untouched.
Three external Rust target metadata deletions were preserved in the named stash
`item7-pre-sync-external-target-metadata`, not included in this change.

A frozen diagnostic Phase 2 producer was used:
`C:/dev/simple-item7-phase2-diag-20261010/simple.exe`, SHA256
`d7acc81607946e437cbb916674109db5fa48da9fa2eefe7c353ba7fe1f95cd87`.
Its existing LLVM Hello receipt is diagnostic-only (source `111968e72bc5`),
not source-matched qualification of this branch. Frozen `--version` exited 0.
The six-product request for this producer remains unqualified, 0/6 products;
BDD callback typing and unavailable Cranelift core-C providers block its full
runner. No Rust seed was substituted.

Three bounded LLVM native-build attempts used the actual literal membership
fixture, private caches, core-C bootstrap runtime, Windows x86_64 target,
180-second process-tree watchdog and 5 GiB RSS cap:

1. `literal-compile`: exit 1, `snapshot-index-drift` for `types.spl` after
   integration edits during preparation. Invalidated by this session's edits;
   this is not evidence of a compiler regression.
2. `literal-clean-compile`: unchanged checkpoint `741f4c5d8a2`; timeout exit
   124, peak RSS 879096 KiB. No native executable or feature execution. Only
   the workaround coverage warning preceded the timeout.
3. `literal-focused-compile`: exact fixture bytes copied into standalone
   `src/main.spl`; exit 1, `git-event-source-unavailable`. The standalone
   fixture lacked Git event metadata. No compilation/feature execution.

Fixture SHA256:
`ef502973d7094a47097f2c4bf5427319717156a0dda1feaad4d705a1543669d8`.
Commands, complete retained streams, exit codes and RSS/owner receipts are in
`C:/dev/simple-item7-phase2-diag-20261010/`; each attempt has a separate
`check-literal*.shs` command and `literal-*-compile` directory. The process
observer's exit 1 for a failed child is distinct from the native watchdog
status (124 for the second attempt). No fourth attempt was made.

The full release-to-working-tree whitespace check passed. Tracked
`doc/06_spec/*_spec.spl` count is zero (checked through Git because this
worktree is sparse). `direct-env-runtime-guard.shs --working` passed.
`check-flat-ast-codec-complete.shs` FAILED: 179 pools examined, with
`par_list_type_import_seen` neither encoded nor decoded. Source comparison
attributes this parser-control-state omission to the release baseline
`f92764f2b97`, not the feature; it still leaves the required guard failing.
The final staged environment-access guard also passed (documentation-only
staged delta). Runtime tests,
SPipe generation, full compiler/lib/MCP checks and bootstrap qualification
remain unverified. The previously documented mutable-link-input receipt gap
and remaining item 7 implementation requirements still prevent stable landing.


## Implementation continuation and independently landed performance fix

On the user's renewed completion request, implemented retained native linker
inputs, completed filter-selectivity publication through the shared process
capture ABI, and serialized the List import parser flag in the combined v4
cache. New source-level regression scenarios are authored but UNRUN. The
core-C capture selfcheck compiled and passed under Ubuntu WSL, including weighted
selectivity, absent versus measured zero, invalid pairs/overflow, and the exact
100000-row boundary. The two Rust edits register the existing runtime ABI name
and signature only; no Rust seed was used to run source tests.

Three new bounded Phase 2 attempts in a committed miniature fixture reached
MIR and native object compilation, but failed linking on runtime packaging
prerequisites. No attempt ran the resulting program. The frozen producer
requires its matching historical runtime tree, not the current feature runtime.
The exact runtime and public ABI-header closure is now staged in a committed
miniature repo; execution stopped at the three-attempt limit. Detailed commands,
input hashes and results: `C:/dev/simple-item7-phase2-diag-20261010/attempt-report.md`.
No admitted full CLI is available, so new compiler/library source acceptance,
SPipe generation, core/MCP smoke checks and bootstrap qualification remain open.

A separately verified guard performance fix landed on `release/1.0` through
PR #2861, merge `3e00bc4161ceec524222f51006584821ffe410b3`:
https://github.com/ormastes/simple/pull/2861 . Eight adversarial fixtures passed;
a same-source WSL comparison improved 23.964s to 10.511s with identical output
and exit status. Its performance note explicitly retains the original baseline
codec findings. This scoped PASS does not qualify item7. General typed/profile
lowering, joins, the other missing applicable P6 observations, grouped receipts
and full source provenance remain incomplete. No full-feature release push or
merge has been made.
