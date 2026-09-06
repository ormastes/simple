# `bcc52735edb` rewound landed work in seven files; six are still unrepaired

- **Filed:** 2026-09-06
- **Class:** stale merge snapshot / anti-revert protocol violation
  (`.claude/rules/vcs.md` § "Sync must never clobber", and the detection recipe
  in `doc/07_guide/infra/vcs/stale_merge_snapshot_rewind.md`)
- **Status:** 1 of 7 repaired. **6 open.** No conflict marker, no failing check,
  no merge conflict — this landed silently.

## What happened

`bcc52735edb` ("Merge remote-tracking branch 'origin/main' into HEAD", in the
PR #261 lineage) produced a tree whose content for seven files matches
**neither parent**. That is the signature of a resolution that pasted a stale
snapshot over the merge rather than combining the two sides: the result is not
"ours", not "theirs", and not a merge of them.

Both parents already carried `0e3bf3f535a` (#273), so the loss was created by
the resolution itself, not inherited from either side. That also means bisecting
on the parents finds nothing.

It was noticed only because `check-runtime-source-list-parity.shs` happened to
watch one of the seven. Nothing watches the other six.

## Detection recipe (reusable)

A merge legitimately differs from each parent — it combines them. What is never
legitimate is content matching neither:

```sh
M=bcc52735edb
git diff --name-only "$M^1" "$M" | sort > /tmp/d1
git diff --name-only "$M^2" "$M" | sort > /tmp/d2
comm -12 /tmp/d1 /tmp/d2          # differs from BOTH parents => invented by the resolution
```

Then, per file, count lines that the origin-side parent had and the current tip
still does not:

```sh
git show "$M^2:$f" | sort -u > /tmp/a
git show "HEAD:$f" | sort -u > /tmp/b
comm -23 /tmp/a /tmp/b | grep -cvE '^[[:space:]]*$'
```

`gained` is not a defect indicator — #261's own forward work shows up there. A
nonzero `lost` is the signal.

## Current state, measured 2026-09-06 against this branch's tip

| file | lines still lost at HEAD |
|---|---|
| `src/compiler_rust/compiler/src/pipeline/native_project/tools.rs` | **0 — REPAIRED** |
| `src/compiler/80.driver/driver_hir_pipeline_lowering.spl` | 34 |
| `scripts/bootstrap/bootstrap-from-scratch.sh` | 22 |
| `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl` | 15 |
| `src/compiler/50.mir/_MirLowering/bootstrap_globals.spl` | 3 |
| `src/compiler_rust/compiler/src/interpreter_extern/gpu.rs` | 2 |
| `src/compiler_rust/compiler/src/pipeline/native_project/tests.rs` | 1 |

77 lines of landed work across six files remain rewound on `main`.

## What was repaired, and why only that one

`tools.rs` lost all three hunks of `0e3bf3f535a` (#273): the
`runtime_memory.c` / `runtime_process_owned.c` / `runtime_coverage_core.c`
seed-list entries, the `-DSIMPLE_RUNTIME_MEMORY_OWNER=1` compile flag, and the
`STAGE4_C_TIME_DEFINITIONS` correction (reinstating the pre-refactor 14 for a
third time). All three are restored. The time-definitions premise was
re-verified rather than assumed: `#ifdef SIMPLE_BOOTSTRAP_TIMESTAMP_COMPAT`
spans `src/runtime/runtime_timestamp.c:58-94` and encloses exactly the 13
symbols the 14-list added beyond the 6, while `rt_time_now_seconds_f64`,
`rt_progress_clock_now_nanos`, `rt_progress_tls_{clear,is_initialized,
start_nanos,store_start_nanos}` are defined unconditionally — so #273's
6-symbol list is precisely the unconditional set and the restore is correct.
`cargo check --release --bin simple` passes afterwards
(`Finished release profile [optimized] target(s) in 50.68s`).

The other six are **not** repaired here, deliberately. They are MIR lowering, a
HIR pipeline driver, the bootstrap script, a GPU extern table and a seed test
file — none is trivially reviewable from a diff, each belongs to a different
lane, and restoring compiler-lowering lines without being able to run the
affected stage is how the rewind happened in the first place. Each needs its
owning lane to confirm the lost lines are still wanted before they go back.

## Limit on the repair that WAS made

`cargo check` proves `tools.rs` is valid Rust. It does not prove the seed's C
archive still links with those three members restored. #273 verified its member
set nm-collision-free, but #261 has since added
`runtime_cache_host_authority_v1.c` to the same list, and
`build_c_runtime_library` runs at native-build time rather than in `build.rs`,
so it cannot be exercised on this host. State of the repair:
**restored to #273's reviewed state; archive link not re-verified here.** The
parity gate's PASS attests list membership, not a clean link.

## Prevention

`.claude/rules/vcs.md` already prescribes the revert guard, and it was not run.
The gap is that it is prose, not a gate. The detection recipe above is
mechanical and cheap (two `git diff --name-only` and a `comm`) and should become
a push-tier row that fails when a merge in the outgoing range contains content
matching neither parent, with an `--expect-invented` escape for genuine conflict
resolutions.
