# `bcc52735edb` rewound landed work in seven files; six are still unrepaired

- **Filed:** 2026-09-06
- **Class:** stale merge snapshot / anti-revert protocol violation
  (`.claude/rules/vcs.md` § "Sync must never clobber", and the detection recipe
  in `doc/07_guide/infra/vcs/stale_merge_snapshot_rewind.md`)
- **Status (2026-09-06, superseded below):** 5 of 7 repaired, 2 closed as
  non-defects — **CLOSED**. See the *Update 2026-09-06* section at the end; the
  original counts and the "Current state" table below are retained as history and
  are now known to be inflated by the detection heuristic. No conflict marker, no
  failing check, no merge conflict — this landed silently.

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

---

## Update 2026-09-06 — remaining six triaged; four repaired, two were never losses

**Status: 5 of 7 repaired, 2 closed as non-defects. This incident is CLOSED.**
Branch `work/repair-bcc52735edb-rewind-2026-09-06`, based on `ab3b27f034b`.

### The "77 lines across six files" figure was inflated by the detection heuristic

The `sort -u | comm -23` recipe above counts *unique line texts* that one side
has and the other does not. It cannot distinguish a lost line from a **reflowed**
one: rewrap an argument list across two lines and both the old and the new
wrapping register as differences. Two of the six were exactly that, and the real
per-file counts are smaller than the table above. The recipe is still the right
cheap detector — it has no false negatives — but every hit must be confirmed
with a real `git diff <merge>^2 <merge> -- <file>` before it is called a loss.

### Per-file verdicts (real diffs, not the heuristic)

| file | heuristic said | real | verdict |
|---|---|---|---|
| `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl` | 15 | 7 sites | **REPAIRED** |
| `src/compiler/80.driver/driver_hir_pipeline_lowering.spl` | 34 | 10 lines (1 hunk) | **REPAIRED** |
| `scripts/bootstrap/bootstrap-from-scratch.sh` | 22 | 8 lines (2 hunks) | **REPAIRED** |
| `src/compiler/50.mir/_MirLowering/bootstrap_globals.spl` | 3 | 4 lines | **REPAIRED** |
| `src/compiler_rust/compiler/src/interpreter_extern/gpu.rs` | 2 | 0 | NOT A LOSS — reflow |
| `src/compiler_rust/compiler/src/pipeline/native_project/tests.rs` | 1 | 0 | NOT A LOSS — rustfmt |

- **gpu.rs**: the merge only re-wrapped the `simple_runtime::metal_graphics_runtime`
  import list. `rt_metal_buffer_upload_raw`, `rt_metal_buffer_download_raw` and
  `rt_metal_set_bytes_raw` are all present on both sides. Nothing to restore.
- **tests.rs**: the merge collapsed one `assert!(...)` from three lines to one.
  Same assertion, same symbol string. Nothing to restore.

### What each repair restores

- **`switch_operators_calls.spl`** — 7 call sites reverted from `if x.?: match
  x.unwrap()` back to `if val v = x: match v`, plus their explainer comments.
  Authored by `9bd924119a0` *"fix(hir,mir): replace 13 stolen-`unwrap` sites with
  `if val` bindings (#298)"* — the stolen-`unwrap` defect class, where any module
  publishing its own bare `unwrap` steals the `Option.unwrap` binding and the call
  returns raw 0. This is a self-hosted-build correctness fix, not a style change.
  Restored file is **byte-identical to `bcc52735edb^2`**; nothing touched the file
  after the merge.
- **`driver_hir_pipeline_lowering.spl`** — the Step 2d block. The merge reinstated
  `# Step 2d: Effect inference pass is skipped in bootstrap empty-HIR mode.` and
  `log_debug("effect inference done")` — a log line that claims a pass ran when
  `run_effect_pass` and `30.types/type_system/effect_pass.spl` do not exist. The
  honest comment plus the `TODO: [compiler][P1] Resolve STUB-002` is restored.
- **`bootstrap-from-scratch.sh`** — see the dedicated section below.
- **`bootstrap_globals.spl`** — `extern fn rt_string_len(value: text) -> i64` and
  its two explainer lines. Without it, `_mir_text_index_of` at :66-71 calls
  `rt_string_len` with no declaration in scope — the unregistered-extern
  silent-nil class (`unregistered_extern_silent_nil_2026-08-01.md`). Authored by
  `928cb25ea92` (#265). Restored file is byte-identical to `bcc52735edb^2`.

### `bootstrap-from-scratch.sh`: what the lost lines do (high-consequence)

This is the sanctioned bootstrap entry point. The merge rewound **two hunks of the
same fix**, `bootstrap_stage2_capability_log_phantom_2026-08-17`, authored by
`dee52cbc42d` / `2dfaae16e88` (#305):

1. `rm -f "${log_dir}/stage2-capability.log"` immediately before the Stage 2
   native-build capability probe. Without it, a log left by a *previous* run
   survives when this run skips the probe (stage 2 failed, or `stage2_bin` is not
   executable) — and the warning below points the reader at it as if it were
   current evidence.
2. The fallback that writes `capability build not attempted: stage2 unusable
   (stage2_status=N)` into that log when the probe did not run and no log exists.
   Without it, `warning: see ${log_dir}/stage2-capability.log` names a file that
   does not exist.

Together these are the difference between "the capability probe failed, here is
why" and a stale or absent artifact silently standing in for current evidence —
the same false-green class the tree-size and seed-build guards exist to stop, on
the one script every bootstrap runs. The surrounding code at `main`'s tip is
unchanged from the merge's version (same lines, +100 offset), so both hunks were
restored verbatim.

### Deliberate supersessions — LEFT ALONE

`driver_hir_pipeline_lowering.spl` also shows 24 heuristic "lost" lines that
`848f626638b` *"feat(stage3): surgical extraction of PR #235"* deliberately
removed **after** the merge: the `streaming_module_surfaces_owner` Option
guard-and-`??` block, replaced by a direct class-typed owner. Those are forward
work on `main`, not rewind damage, and were not restored. Same for 15 lines in
`bootstrap-from-scratch.sh` removed by the later stage3-provenance work. Every
residual line was mechanically confirmed to appear as a `-` line in
`git diff bcc52735edb HEAD -- <file>`; none is unaccounted for.

### The record's "both parents already carried `0e3bf3f535a`" claim is wrong

Measured: `bcc52735edb^1` does **not** contain the STUB-002 text; `^2` does; the
merge base `a24698865f4` does. So the topic side had already lost the content
before this merge, through an earlier merge in its own chain
(`2e9e1b15b4e "merge: bring origin/main into session/path-file-lane-2026-…"`
and ancestors — the string appears in zero of the 40 most recent first-parent
commits on that side). `bcc52735edb` **propagated** a rewind it did not
originate. That matters for detection: a scanner keyed on the originating merge
will not flag `bcc52735edb` at all.

Confirming that all four are genuine losses rather than supersessions, stated as
what was actually proved:

- The four regions are untouched in `git diff bcc52735edb origin/main`, and none
  of the four strings appears in any of the 209 commits of
  `bcc52735edb..origin/main`.
- A whole-history `git log --no-merges -S` on each string returns the *authoring*
  commits — `9bd924119a0` (#298), `928cb25ea92` (#265), `dee52cbc42d`/`2dfaae16e88`
  (#305), `7cd60dfd3fc`/`d2413241a1f` (#307) — plus two **whole-tree snapshot
  commits**, `e09f6b9ac66` ("fix(io): serial_close is idempotent", 401,176 files
  changed, 93M insertions, an ancestor of `main`) and `01208a07c8d`
  ("metrics(gpu)", 134,299 files changed, 46M insertions, *not* an ancestor of
  `main`). Both appear in three or four of the four `-S` lists, which no
  serial_close or GPU-metrics change legitimately does. They are additions, not
  removals, so they do not weaken the conclusion — but they are the non-merge form
  of the same defect class `vcs.md` § "Sync must never clobber" warns about, and a
  scan restricted to merge commits will never see them.
- Attribution correction: **`0e3bf3f535a` (#273) does not touch any of these four
  files.** #273 authored `tools.rs`, the one already repaired. The four restored
  here come from #298, #265, #305 and #307. The reference used throughout this
  triage is therefore `bcc52735edb^2` — the exact `origin/main` content the merge
  was given and discarded — not `0e3bf3f535a`.

One forward-looking note: the unlanded lane `work/stub-002-effect-inference-2026-09-06`
(`cbbd1dbc056`, "withdraw STUB-002 — delete the orphaned effect solver") deletes
exactly this restored block, and is based on a tree that still had it. Restoring
it on `main` makes that lane's landing a clean delete instead of a conflict or a
silent reintroduction.

### Wider exposure: this is not the only stale merge

Scanning the last 400 commits of `origin/main` (152 merge commits) for the
signature *"content the origin-side parent gained since the merge base, which the
merge result does not contain"*:

**8 merges match. 6,236 lines they dropped are still absent from `origin/main`.**

| merge | date | dropped at merge | still lost at tip | product files still lost |
|---|---|---|---|---|
| `0547effe615` | 2026-08-27 | 4123 | 3900 | 1 |
| `a7fd32f9475` | 2026-09-02 | 4423 | 2178 | **114** |
| `198737a06e9` | 2026-09-06 | 57 | 57 | 2 |
| `66e58d62da8` | 2026-09-02 | 57 | 57 | 2 |
| `d150a169f26` | 2026-08-31 | 35 | 35 | 1 (`src/runtime/runtime_simd_dispatch.c`) |
| `df31df530e7` | 2026-09-06 | 4 | 4 | 1 |
| `dfb069ade84` | 2026-09-05 | 4 | 4 | 1 (`bootstrap_globals.spl`) |
| `cb986e09bdb` | 2026-09-04 | 1 | 1 | 1 |

Caveats, stated rather than papered over: most of the two large counts are test
files, and a line "still lost at tip" can also be a line something later deleted
on purpose — this signature over-reports, exactly as the record's own recipe
does, and each hit needs the same real-diff confirmation applied above. **8 is
also a lower bound**, because it counts only merges that *originated* a rewind:
`bcc52735edb` itself does not appear, since it propagated one. None of these
eight is repaired here — the user scoped this session to the seven files.

One of the eight was hand-checked and is a **false positive**, which is worth
recording because it shows the failure mode of this signature. `dfb069ade84`'s
4 "lost" lines in `bootstrap_globals.spl` are a 4-line comment about
`current_module_id` initialisation on the flat bootstrap route. The merge did not
drop it — it **replaced** it with a longer comment that quotes the old text
verbatim, credits the upstream PR (#369) that reached the same conclusion, and
adds the concrete mechanism (`record_external_layout_reference_resolved`'s
self-owner filter degenerating to `not candidate.starts_with("::")` when the id
is empty). That is a deliberate supersession and a strict improvement; it is
left alone. It is *not* related to the `rt_string_len` extern repaired here,
which reached the same file by a different route. Each of the seven remaining
hits needs the same hand-check before anyone acts on it.

The prevention item at the end of this record — make the detection recipe a
push-tier gate — should be read against these numbers, not against one incident.
