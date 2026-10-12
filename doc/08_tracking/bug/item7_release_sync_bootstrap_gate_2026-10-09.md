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

## Retargeting to release_phase3 (2026-10-11)

The user explicitly selected GitHub `release_phase3`. Its fetched base is
`20f619fe31baa4decbe40f6d367fb5e4f115bbd8`. Recovered all 42 local commits
from `aadc8b216b0` into the isolated, locked worktree
`C:/dev/simple-item7-phase3-20261011`, branch
`work/item7-release-phase3-20261011`, and rebased them onto that base.
The old `work/item7-sync-20261009` branch remains a recovery reference.
No unrelated changes from the shared checkout were included.

Conflicts were reconciled to retain Phase 3 imported-generic parsing, explicit
call type arguments, and builtin MIR method lowering alongside the item7
adaptive type and membership paths. The combined serialized pool schema is
`spl-flatpool-v7`; neither upstream v6 nor the old feature v4 has this layout.
Cache fixture payloads now use v7. Imported types take precedence over the
unimported AdaptiveMap/AdaptiveSet fallback. Both paths consume the same parsed
argument list. Further integration validation and source tests remain required.

Executed the canonical artifact gate from the isolated checkout:

```sh
sh scripts/check/check-bootstrap-stage3-selfverify.shs \
  --output-dir /c/dev/simple/build/bootstrap --full-provenance
```

Its seven internal adversarial fixtures behaved as specified, but the actual
artifact check reported `stage3_selfverify_reason=no_stage3_provenance_manifest_found`
and `ERROR — nothing was checked` (wrapper exit 1). The gate source is unchanged
between the old base and the selected Phase 3 base. This establishes missing
admission evidence, not a compiler or feature PASS. The shared checkout's
nearby Stage 2 candidate is tied to an older source and failed its frontend
sanity check; it cannot substitute for a source-matched admitted compiler.

STATUS: BLOCKED for Phase 3 admission and full item7 verification. The remaining
implementation gaps described above also remain open. Push this work only as
an unfinished PR targeting `release_phase3`; merge requires passing admission
and the required source acceptance checks. Do not relabel gate self-tests,
static source checks, or a narrow native capture selfcheck as Phase 3 PASS.

The native capture selfcheck compiled with assertions enabled against this
worktree's runtime. An initial shell wrapper lost the exit-status fields;
its result was not accepted as PASS. One corrective direct WSL invocation of
the already-built binary returned tool exit 0, without recompilation. Logs:
`build/item7-phase3-capture-20261011/`. The only compile diagnostic was an
unrelated ignored `write()` return value in the HTTP probe. Binary SHA-256:
`4e2321d1eb7e4cc72d5c6322e7950ce2f752bcb96e24c14e00fb1d82d99b9f65`;
capture owner header SHA-256:
`daac21a7e97e2dc68344ff2609dd8a0805de7a890a332103a31d96ba902ae594`.
This scoped native runtime result does not execute the Simple wrappers or
qualify the compiler.

Final source integration check: `check-flat-ast-codec-complete.shs` returned
exit 0, `PASS — 184 pool(s) checked, all encoded and decoded`, within its
120-second bound. Working environment and numbered-artifact guards passed.
The tracked file count increased from the target's 143288 to 143323 (35 feature
additions), with no target-relative file deletions; tracked executable specs
under `doc/06_spec` remain zero. Imported-registry graph and roundtrip tests
are authored, not executed. These source checks do not change the admission
BLOCKED status.

## 2026-10-11 bounded current-source compiler continuation

The lane was synced onto `release_phase3` commit `9434873b8d3`, including its
cold-HIR dictionary guard. Feature commit `33c674a55b518b20679a21acd481d5f410d0b29b`
adds an explicit observed adaptive text-set loop API and the shared completed
loop-trip capture ABI. Its C selfcheck compiled and ran with exit 0; the ten
new Simple unit cases and standalone probe remain UNRUN.

Two source/runtime-pinned pure-Simple LLVM compiler diagnostics were executed
without seed fallback. The first timed out at 900 seconds (exit 124, no binary)
after its HIR warm worker reported zero failed modules. The changed second
attempt reused that cache, skipped HIR warm-up and reached the final worker,
but exceeded the enforced 5 GiB process-tree cap (exit 88, no binary).
Both receipts confirm quiescent process trees and clean frozen source.
Exact inputs, outcomes and retained evidence are recorded in
[the interpreted-worker timeout report](item7_phase3_interpreted_worker_timeout_2026-10-11.md).

STATUS: BLOCKED for Phase3 admission and full feature acceptance. Hello World
native sanity, the standalone loop probe and required compiler/lib/MCP checks
cannot be marked PASS without a working source-matched runner. General compiler
loop identity/instrumentation and broader typed joins remain implementation gaps.
PR #3073 targets `release_phase3` and must remain unfinished/unmerged.
