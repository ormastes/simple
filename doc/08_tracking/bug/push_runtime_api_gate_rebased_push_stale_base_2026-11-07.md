# push-runtime-api-regression charges upstream removals to a rebased force-push (stale base 1dc81da08c2)

- **ID:** `push_runtime_api_gate_rebased_push_stale_base_2026-11-07`
- **Status:** Failed-fetch repair verified locally (2026-11-10); canonical bug shard tracks review/landing.
- **Priority:** P2
- **Area:** `scripts/check/check-push-must-pass.shs` (`rebased_push_published_base`, ~line 1304), which feeds `check-runtime-api-regression-push.shs`

## Symptom

A records-only commit (changes under doc/08_tracking/bug only) was rebased onto
origin/release/1.0.0 and force-pushed with `git push --force-with-lease` (normal hooks)
to its existing PR branch `work/w-scvrec-20261107` (PR #7518). The push failed twice,
with a fresh `git fetch origin` before each attempt:

```
check-runtime-api-regression-push: FAIL — 3544 symbol(s) checked in 1dc81da08c2f5cad4fc499433747345c0549278e..91a57269017427fde6c0ac9cd07856c9d5b4b61a, 6 symbol(s) removed: rt_core_dict_read_advance rt_core_dict_scope_read_heap_v1 rt_core_dict_sort_entry_less rt_dir_remove_all_wide_impl rt_native_closure_payload rt_secure_temp_dir_slot_from_value
push-must-check: gate push-runtime-api-regression exit=1 255292ms
```

The first attempt used the same base with tip `05c57b4368292f3df439c76cd94d4307d9311d77`.

`1dc81da08c2` is "Merge pull request #4680 from ormastes/work/semantic-lint-dispatch-20261025".
It is an October ancestor of release/1.0.0. It is not the merge-base with release/1.0.0,
which is the release tip itself (the parent of the pushed commit). The six removals had
already landed upstream through PRs, and the pushed commit touches no runtime source.

The same content pushed as a NEW ref with upstream `release/1.0.0` goes through
`new_ref_published_base` and gets the correct base.

## Suspected cause

For a non-fast-forward push, `rebased_push_published_base` picks the published line
(main / release_phase3 / release/*) whose merge-base gives the fewest commits. It skips
any line whose remote sha is not present locally. release/1.0.0 advances every few
minutes, so its ls-remote sha is often not yet fetched. The line is then skipped and
the old main-side merge-base wins.

## Expected

For a branch whose upstream is release/X, use the merge-base with that release line.
If the remote sha is missing, fetch it or fail closed with "fetch first", as
`new_ref_published_base` does. Never fall back silently to a different line's merge-base.

## 2026-11-10: failed-fetch path reproduced and repaired

The release baseline `6d496f82c5acabc2fc52b2b78146272e664dc371` already
fetches a missing advertised protected-line object. However, when that fetch
fails, `rebased_push_published_base` still returns an available older main
candidate. `new_ref_closest_published_base` also masks a refused live query by
falling back to the local `origin/main` merge-base.

The retained local-Git reproducer creates main, a release descendant, a feature
commit, and an advertised remote-only release advance. It injects only a failed
object transfer, leaving the advertisement and merge-base operations real.
Before the repair, both entrypoints returned the main SHA and the regression
exited 1. After the repair, both refuse and the same regression exits 0.

The repair refuses an incomplete protected-base comparison, prints the existing
`run git fetch first` diagnostic, and preserves that refusal through the new-ref
wrapper. Available unrelated histories are still ignored by merge-base failure;
arbitrary non-protected refs never enter the candidate set. A missing object
cannot be assumed unrelated until it is fetched. No gate verdict, range bound,
or protected-ref policy is weakened.

Verification runs on Windows using Git Bash and actual disposable Git
repositories, without a Simple compiler. `--self-test-release-base` now covers
failed transfer through both entrypoints, empty result output, the diagnostic,
and the successful on-demand fetch through both entrypoints, alongside the
existing main/release/legacy and actual-push-endpoint controls.

Retained evidence in `C:/dev/wt/g100-vcs_provenance/build/evidence/`:

- `release-base-baseline.log`: exit 0, 24 preexisting PASS assertions.
- `stale-base-red.log`: exit 1, both stale-main selections reproduced.
- `stale-base-green.log`: exit 0, both original failure paths refuse.
- `release-base-fixed.log`: exit 0, 25 PASS cases in the expanded integration suite.
- `env-working.log`: direct environment/process boundary guard PASS.

These are shell push-range tests, not self-hosted compiler or RISC-V release
qualification. The separate seed-attribution bug remains dependent on bootstrap
and correctly attributed RISC-V gate execution.

Provider input/output/cache-read/cache-create token usage: **unavailable**.
Comparable cohort average: **unavailable**. Usage ratio: **unavailable**; no
estimated or zero-filled accounting values are claimed.
