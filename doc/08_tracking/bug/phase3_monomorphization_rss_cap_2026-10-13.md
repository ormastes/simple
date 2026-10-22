# Phase 3 compiler monomorphization crosses the 8 GiB RSS cap

Status: OPEN. The three-attempt diagnostic lane is terminal; no Phase 3 compiler executable, provenance or Hello World acceptance exists.

## Exact native evidence

Source HEAD `3f5200fd34d9a205381a592c3fec6304fa058c4b`; frozen pure-Simple Stage 2 producer SHA256 `4812f6ed17fe51ef0bd36fdd5d6f02d2871d7f6c14a9b468bed209016f33be77`; Linux AArch64, Cranelift, one worker, isolated retained caches. The focused entry is `src/app/cli/bootstrap_main.spl`, using the compiler/CLI/library roots and materialized imported plugin owners. Direct diagnostic admission is NONE.

Attempt 1 failed missing sparse plugin inputs. Attempt 2 crossed the 3 GiB cap after 1220.54 seconds during HIR. Attempt 3 used the same producer/source/cache authorities with an 8 GiB cap and 7200-second deadline, and terminated at RSS exit 88 after 1678.67 seconds. Peak observed tree RSS: 8,390,084 KiB; watchdog cap: 8,388,608 KiB; descendant quiescence: verified. GNU time reported 8,390,724 KiB maximum process RSS.

All 1293 HIR modules completed. The final HIR snapshot at 1,654,814 ms records 1,838,614,386 tracked live heap bytes and 6,365,204 KiB RSS. Source reclaim then records 1293 sources and zero retained source owners. The next phase marker is `phase4:monomorphize:start` at 1,654,862 ms; no matching done marker exists. The RSS guard terminates approximately 24 seconds later. This localizes the failed phase boundary, but does not attribute allocations or prove an individual monomorphization defect. It is not an object-generation or compiler-link success.

## Repair and qualification handoff

1. Preserve the frozen producer, exact source input manifest, valid cache prefix, HIR/memory/progress records and all failure receipts. No key rewriting, placeholder objects or disabled resource enforcement.
2. Review the monomorphization handoff and full-body graph ownership on the frozen producer against the current source. Current `driver_orchestration.spl` selects either archive-backed phase 4 or retained `monomorphize_impl`; authored archive/lease code is not evidence that this older immutable producer executed it.
3. Build a coherent corrected pure-Simple Stage 2 through the canonical bootstrap/admission flow; preserve compatible seed caches. A source repair only affects a new compiler containing it. Seed use remains bootstrap-only, and no default Rust tool substitution is permitted.
4. With an explicit additional verification budget, run one changed-producer qualification in this existing session worktree and private output. Retain independent failures and valid successes. Require authenticated compiler objects, genuine link and compiler-built/executed Hello World. Then qualify the failed changed-entry cache workload and complete every remaining incremental-plan gate.

Evidence root: `.simple/storage/build/phase3-incremental-completion/`; terminal summary is `evidence/phase3-terminal-summary.json`. The 1293 HIR completions do not increase the sealed legacy object PASS total. Other worktrees and active lanes remain untouched. No push occurred.

Owner: Codex phase3-incremental-completion session. Reviewable mitigation: use a coherent repaired producer and bounded graph ownership; this report does not authorize a fourth equivalent run or another RSS ceiling increase.

## Bootstrap compatibility correction to the handoff

Static review of the current selector found an essential boundary: `driver_hir_archive_production_requested_v1` in `driver_orchestration.spl:83` requires `SIMPLE_BOOTSTRAP != 1`, while the retained Phase 3 argv/environment requires `SIMPLE_BOOTSTRAP=1`. The archive controller additionally requires an actual selected managed-runtime owner before producing its bounded HIR journal. A source rebuild alone therefore does not establish that Stage 3 will enter that path.

The next repair must either bound the retained bootstrap HIR-to-Mono handoff with genuine per-module ownership, or qualify a bootstrap-compatible archive producer/runtime owner and its complete inventory/publication/semantic dependencies. Preserve the existing strict admission gates, runtime selection and cache witnesses. Removing the selector guard or changing the environment without qualifying the required owner is not a repair. Authenticate the new producer and demonstrate the actual selected route before another full-tree qualification.

Review evidence: `evidence/bootstrap-archive-compatibility-review.json`. This is a static compatibility finding; no new build or additional verification cycle was started. The original full incremental and Phase 3 goal remains unmet.

## Parallel repair candidate (2026-10-14)

The user authorized parallel memory/logic repair and a further changed-producer qualification. The retained Mono candidate canonicalizes only signatures during generic discovery, retains the original body once, and applies the complete body recipe after a concrete specialization request passes deduplication and nominal transport. It also removes writes into the unused legacy engine and combines final placement/pruning, releasing completed rewrite tables. Public pass layout and archive/runtime admission guards remain intact.

Production scope: `src/compiler/40.mono/mono_archive_types_v1.spl` and `monomorphize_integration.spl`. Independent source review found signature/type-parameter/linkage equivalence with the full recipe. Authored demand/signature regression tests and a cross-module native fixture remain unexecuted. Original and rewritten roots are still retained; bounded full-tree RSS and compiler object/link completion are not established by this source patch.

A canonical seed-backed Stage 2 refresh is prepared in `.simple/storage/build/phase3-producer-refresh`. The copied immutable seed passed byte/fingerprint checks and the wrapper skipped Cargo, but its first launch stopped at preflight source-authority admission before compilation. Preserve this refusal and restore missing pinned tracked roots before retrying the changed-input prerequisite. The full additional Phase 3 qualification has not started; the original three failed diagnostics remain terminal.
