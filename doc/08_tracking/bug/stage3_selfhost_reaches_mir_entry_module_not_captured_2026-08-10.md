# Stage-3 self-host reaches MIR lowering for the first time — new blocker: entry HIR module not captured in the flat accumulator

- **ID:** stage3_selfhost_reaches_mir_entry_module_not_captured_2026-08-10
- **Status (2026-08-17, W1 source re-check):** the fix is PRESENT in current
  source; validation still pending. The entry module is no longer registered
  under `module.name` (a physical path such as `src/app/cli/bootstrap_main.spl`,
  which is why a `contains("bootstrap_main")` scan over the 572 captured names
  found the *file* absent under its *logical* name): at
  `src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl:1936-1938`
  `registry_module_name` is now
  `hir_module_logical_name_from_path(self.module_filename)` when `is_entry`, and
  `module.name` otherwise — so the captured key is spelled the same way as the
  `entry_module_name` that `bootstrap_lower_flat_hir_modules_to_mir_for_target`
  compares against. Same call site also fixes the sibling row
  `stage3_selfhost_entry_module_zero_functions_2026-08-11` (functions now come
  from `lowered_module.functions.values()`); treat the two as ONE defect family:
  "the entry module's identity and body are both lost when rebuilt through the
  global flat accumulator". Not re-reproduced here — needs a full stage-3 run.
- **Status (historical):** FIX CANDIDATE PUSHED, VALIDATION PENDING. Milestone: after landing
  `17a55168a11`, `7dd296f2ef6`, `1f81b2b4f0b`, `67055c4d3f1` (this session) plus
  a large flurry of peer-session fixes tonight (`6834081f503` through
  `b1c1bb1045b` — HIR diagnostic isolation/preservation, layout dedup, etc.),
  Stage 3 self-host gets **past phase-3 HIR errors entirely for the first time
  ever** (`[bootstrap-error-count] ... count=0` at every checkpoint) and
  reaches `[driver-mir] bootstrap flat:start` — MIR lowering — which has
  **never** been reached in ~15+ campaigns run over the preceding 24 hours.
  It then hits a new, clean, diagnosed failure (not a crash):
  `error: bootstrap flat HIR entry module was not captured: app.cli.bootstrap_main`.
- Area: `src/compiler/50.mir/_MirLowering/bootstrap_globals.spl`,
  `bootstrap_lower_flat_hir_modules_to_mir_for_target`.

## The failure

```
[driver-mir] bootstrap free:start
[driver-mir] bootstrap flat:start entry=app.cli.bootstrap_main modules=572
error: bootstrap flat HIR entry module was not captured: app.cli.bootstrap_main
```

`bootstrap_lower_flat_hir_modules_to_mir_for_target` scans
`bootstrap_hir_module_count()` (572) entries, normalizing each captured HIR
module's raw path via `bootstrap_mir_logical_module_name()` and comparing
against `entry_module_name` ("app.cli.bootstrap_main", passed in literally).
None match, so `entry_index` stays `-1` and the driver exits 1.

## Investigation (three rebuild cycles, each narrowing the search)

1. Printed the first 5 and last 5 captured module names + their normalized
   form. None were `app.cli.bootstrap_main`, but the sample only covers 10 of
   572 — inconclusive on its own.
2. Extended to a full substring scan (`raw.contains("bootstrap_main")`)
   across all 572 captured modules: **`found_any=false`**. The entry module's
   source file is **not among the 572 captured HIR modules at all** — this is
   not a name-normalization mismatch (the four-copies-must-stay-byte-identical
   risk this file's own comments warn about), it is an **absence**.
3. Added an unconditional `eprint("[entry-miss-scan] idx0-raw=" +
   bootstrap_hir_module_name_at(0) + "\n")` immediately after the `found_any`
   print (which itself printed correctly) — **it never printed**, on a build
   that used the exact same eprint-with-string-concatenation pattern that DID
   print correctly for `idx=1..4` and `idx=567..571` in the prior rebuild
   cycle. This rules out the general "eprint + text parameter" defect
   documented in
   `stage3_selfhost_phase3_error_array_index_after_struct_reassign_silently_noops_2026-08-10.md`
   (concatenation worked fine for other indices in the same file/pattern) —
   whatever is wrong with `bootstrap_hir_module_name_at(0)` specifically is a
   **different, narrower** defect: either the call for index 0 hangs/traps
   silently, or its return value has some property (not just its concatenated
   presence) that breaks the subsequent `eprint`.

## What this means

Given `found_any=false` across the full 572-entry accumulator, and that the
"572" figure itself is a coincidence with the earlier-observed HIR-error count
from before tonight's fixes (unrelated — that number is simply the total
module count in this closure, confirmed by the `[driver-mir] ... modules=572`
line), the real defect is upstream of this lookup: something in the flat-HIR
accumulation pipeline (the phase that populates `_bootstrap_mir_functions` /
whatever backs `bootstrap_hir_module_count()`/`bootstrap_hir_module_name_at()`)
either never adds the entry module, or adds it under index 0 in a form that
can't even be read back safely (given the idx=0 print anomaly above).

## What was and was not done

- **Done:** confirmed via three independent rebuild-and-verify cycles that
  (a) phase 3 now passes cleanly with 0 errors — first time ever, (b) MIR
  lowering is reached — first time ever, (c) the entry module is absent from
  the 572-module flat accumulator, not merely misnamed, (d) index 0
  specifically resists a print that works fine for other indices in the same
  loop shape.
- **Not done:** did not find where modules are added to the accumulator
  (`bootstrap_hir_module_count`/`bootstrap_hir_module_name_at`'s backing
  store) to check whether the entry module is explicitly skipped, added
  under a different key, or lost to an index-0-specific defect. Did not
  determine whether the index-0 print anomaly is a symptom (index 0 holds
  corrupt/uninitialized data) or a separate, unrelated defect. Did not
  attempt a fix — time budget was spent entirely on repro and narrowing,
  given the milestone significance and how much peer-session activity is
  already flowing through this exact code path tonight (see
  `stage3_selfhost_nil_receiver_sigill_in_lower_expr_caller_2026-08-05.md`
  for the original target bug, still not reached — MIR lowering must first
  succeed for the entry module before that fault site is even reachable).

## Suggested next step

Find the accumulator's write side (likely a `bootstrap_hir_modules_add`-style
function paired with `bootstrap_hir_module_count`/`bootstrap_hir_module_name_at`
in this same file or a sibling) and check: is the entry module explicitly
excluded (e.g. an `if is_entry: continue` during flat accumulation, on the
assumption it's handled separately), and if so, is `entry_module` supposed to
be looked up through a different accessor than this generic scan uses? Given
how fast this area is moving (peer commits landing every few minutes tonight),
re-check `git log --oneline -20 -- src/compiler/50.mir/_MirLowering/
bootstrap_globals.spl` before starting — this may already be fixed by the time
this doc is read.

## 2026-08-11 continuation: scalar ownership and zero-function entry

The suggested write-side investigation above was completed. Entry ownership
is now represented by a scalar registry index rather than a second module-name
search, and MIR consumes that index directly. The resulting receipt proved
that the entry row is present and readable:

```text
[bootstrap-flat-entry] index=0 modules=573 functions=0
error: bootstrap entry lowered to 0 MIR instructions (ret-0 stub module)
```

This supersedes the earlier conclusion that the entry row was absent or that
index 0 was unreadable. The row exists, but its parser/HIR function collection
is empty. HIR diagnostics remained clean at all recorded checkpoints.

### Fixes pushed

- `27c67653759` materialized registry functions directly from
  `lowered_module.functions.values()` instead of reconstructing them through
  the global bootstrap function accumulator. The next receipt remained
  `functions=0`, proving the authoritative `HirModule` was already empty.
- `84b8f601128` excluded ephemeral Codex `*/.codex/tmp/arg0/*` PATH shims from
  bootstrap tool authority. Those directories existed at startup but vanished
  during long Rust builds, causing `could not bind bootstrap tool authority`.
  A later cycle passed this authority gate and entered Stage 2/3.
- `5a4bf40c007` changed the bootstrap entry HIR branch to reparse authoritative
  source content immediately before lowering instead of trusting a non-nil,
  arena-backed phase-2 `ParserModule` whose `functions` dictionary was empty.

An executable regression spec was also added at
`test/03_system/compiler/bootstrap_stage3_real_body_spec.spl`. It requires an
explicit pure-Simple Stage 3 binary, uses the canonical bare positional entry,
builds a helper-calling program, executes the artifact, and checks a marker
computed from the helper result so a link-valid ret-0 module cannot pass.

### Validation status

The last completed cycle before `5a4bf40c007` again reported
`index=0 modules=573 functions=0`. A post-fix incremental validation cycle was
started and completed its Rust seed rebuild, but was intentionally interrupted
with exit 130 when work was narrowed to documentation only. Therefore the
fresh-entry reparse is a pushed fix candidate, not a verified Stage 3 PASS.

The next session should run one incremental debug bootstrap, retain the new
`[bootstrap-flat-entry]` receipt, and require `functions > 0` before proceeding
to Stage 4. Do not cite the older zero-function log as evidence against
`5a4bf40c007`; it predates that fix.

---

## Triage re-verification 2026-08-17 (c_mir lane, classified by CONTENT not SHA)

**Governing fact for every 50.mir-attributed row:** nothing runnable on this
host executes `src/compiler/50.mir/**.spl`. `bin/simple` resolves to
`bin/release/x86_64-unknown-linux-gnu/simple` (59536728 bytes, mtime
2026-08-16 22:59), whose own `--version` banner states it is a Rust
**bootstrap seed**; it has its own Rust MIR/JIT/native pipeline and never reads
`src/compiler/**.spl` for compilation logic. `bin/release/simple` is the
2181-byte refusing production-guard wrapper, and no stage2/stage3 self-hosted
binary exists under `build/bootstrap/`. Therefore any evidence in this doc
phrased as "reproduced on `bin/simple`" is evidence about the **seed**, not
about 50.mir, and the runtime claim here can only be closed by a full
self-hosted bootstrap (not run: the user's bootstrap is live and
`build/bootstrap/**` is off-limits). Rows were therefore classified by
grepping current source.

**Verdict: FIX PRESENT IN SOURCE; runtime claim UNVERIFIED (needs stage3).**

`src/compiler/50.mir/_MirLowering/bootstrap_globals.spl:396`
`val entry_index = bootstrap_hir_entry_index()` (the scalar registry, imported at
`:23`) replaces the name scan, and `:398` `if entry_index < 0:` now guards the
"was not captured" eprint fail-closed. The `functions > 0` receipt this doc asks
for still requires one incremental debug bootstrap, which was not run here.
