# Stage 2 receiver probe intermittently loses `compiler.common.module_path_naming` (NOT_RUN)

- **Filed:** 2026-09-14
- **Status:** OPEN — intermittent, not bisected (2026-11-11 lane boot18: same base+flake pair as the NOT_RUN record; attribution FIXED and verified, transient stays OPEN — see addendum)
- **Severity:** blocks a bootstrap lane non-deterministically
- **Lane:** macOS arm64, F74 round 3, worktree `agent-affc884d75d16fbde`, tip `def2a9c30a1`

## What happened

Two Stage 2 trust-root runs were launched from the SAME tree, the SAME seed and
the SAME command line:

```
sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2 \
   --mode=dynload --jobs=half --produce-stage3-receipt=verify-landed-compiler-fix
```

Run 1 (`build/f74logs/stage2-run1.log`) FAILED the Stage 2 receiver probe:

```
stage2-sanity.env  status=pass  (version 1.0.1-beta.1)
stage2-receiver.env status=fail probe_exit=1
error: stage2 failed the positional pure-Simple Stage-3 route (status 1)
error: in-process native-build: build failed: 0 failed, 0 unverified, 1 not run,
       1 ok of 2 unit(s) - NOT_RUN: compiler.common.module_path_naming
```

The reason the compiler itself recorded for the lost unit was
`never started (build ended first)` (`src/compiler/80.driver/driver_build/build_outcome.spl:257`).

Run 2 (`build/f74logs/stage2-run2.log`) PASSED the same probe and admitted
Stage 2 (sha256 `a8a30e99f9e32ca68d8fdce98bfaca353df7fbcd6e4cdf2298ebddd71042864d`).

## Why this is a defect and not a red build

`0 failed, 1 not run` is a scheduling outcome, not a compile error: the unit
never started because the build ended first. A two-unit build that ends before
its second unit starts is a driver/scheduler race, and it is nondeterministic
across identical inputs. The probe is correct to refuse a build that did not
run everything it planned — **do not relax the probe**, and do not treat a
NOT_RUN as a pass. The fix belongs in whatever ends the build early.

## Not bisected

A lead was noted but never confirmed: the pre-#921 orphan lane passed this exact
phase (`bootstrap_stage2_positional_stage3_route=PASS`), and #921's only seed
change is `native_project/mangle.rs` while the lost unit is
`compiler.common.module_path_naming`. That is a coincidence of names, not
evidence; nothing was bisected.

## Repro

Not reliably reproducible. 1 failure in 2 runs on this host. Re-running the same
command was sufficient to get past it.


## 2026-11-11 addendum (lane boot18, work/p3-boot18-20261111) — same pair as the NOT_RUN record; transient stays OPEN

This flake is the same underlying transient as
`stage2_receiver_probe_module_path_naming_not_run_2026-09-14.md` (base+flake
pair, triaged together 2026-11-11). The `never started (build ended first)`
reason the compiler recorded here was the misattribution the 2026-09-14 fix
corrected: the sequential concurrency-1 build DID start both units (llc
resolved once per module in the log this doc quotes), so a genuine "build ended
first" race was never the mechanism. The real defect was an outcome that was
never recorded plus a capsule receipt invariant rejected only on a later look;
both halves are now covered:

- Attribution: FIXED + verified — `native_attempted_unit_outcome_recorded_spec.spl`
  **4/4 GREEN** on the tracked seed (see the base record's 2026-11-11 addendum
  for the mechanism and code sites).
- Mechanism: the site-10 frozen-source-identity fix is pinned green
  (`native_capsule_source_identity_survives_eviction_spec.spl` 7/7), but it
  predates this flake (2026-09-12 vs 2026-09-14) and does not by itself close
  the intermittent `uncached_names[0]` edge this record hit.

Verdict: transient stays OPEN (Status unchanged); not reproducible in this lane
(1 failure in 2 runs on the original host; this doc's own repro note says
re-running was the only workaround, and there is no repro smaller than the
~90 min Stage-2 trust-root lane). A recurrence now fails NAMING the invariant
instead of surfacing as a false NOT_RUN — keep the probe fail-closed.
