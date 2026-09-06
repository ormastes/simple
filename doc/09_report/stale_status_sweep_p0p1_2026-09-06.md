# Stale-status sweep over the open P0/P1 bug rows — 2026-09-06

**Scope.** The 272 actionable-on-this-host open P0/P1 rows in
`doc/08_tracking/bug/bug_db.sdn` (input list `/tmp/tri/pkg/stale_candidates_p01.txt`,
format `SEVERITY | id | file | reproducible_by`). All 272 carry `status: open`
in the DB today — verified by extracting the `bugs` table's status column, which
returned `272 open, 0 anything-else`.

**Nothing in the tracking DB, in any spec, TODO or feature was edited.** This
report only RECOMMENDS. The two harnesses added by this lane write exclusively
under `build/sweep/` and are wired into no gate.

---

## 1. Provenance

| | |
|---|---|
| Host | aarch64 Linux, 20 cores, 121 GiB RAM |
| Binary | `bin/simple` -> `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (symlink created read-only in this worktree; the shared binary was never replaced) |
| Binary identity | 50,093,192 bytes, mtime `2026-09-06 09:59:11 +0900` |
| Binary self-report | `WARNING: this Rust-built Simple binary is a bootstrap seed only` / `Simple Language v1.0.0-rc.1` |
| Worktree HEAD at sweep start | `660402470ae` (branch `work/stale-status-sweep-2026-09-06`) |
| Load average at start / end | `33.28` / `26.07` (a bootstrap and ~10 other sessions share this box) |
| Concurrency cap | 4 test processes (`SWEEP_JOBS=4`) |
| Per-row wall budget | 420 s (`SWEEP_TIMEOUT=420`) |
| Measured cost of one spec | 4.0 s wall for a 12-example crypto spec — **not** the 1-3 min budgeted, and not the ~310 s `Session setup` cost quoted for whole-suite runs in `.claude/rules/commands.md` |

**Side effects the sweep DID cause, and their reversal.** Running 155 real
repros is not free: three of them write to the tree. `bin/simple run
test/perf/db/db_bench_driver.spl` (the JIT-lane run of
`interp_run_cross_module_db_option_mutation_2026-06-13`) rewrote
`doc/09_report/perf/perf_baseline_db_2026-06-13.md` and
`doc/10_metrics/perf/perf_baseline_db_table.md`;
`scripts/check/check-portable-compute-toolchains.shs` created
`doc/09_report/portable_compute_toolchains_2026-09-06.md`; and one repro
dropped a binary-named junk file in the repo root. All four were reverted
(`git checkout --` on the two tracked docs, delete on the two untracked files)
and `git status --short` in this worktree is clean apart from this report and
the two harness scripts. Anyone re-running this sweep should expect the same
four and revert them the same way.

Side-effect check, run before the fan-out: a single `bin/simple test <spec>`
left `git status --short` **empty** in this worktree, and the shared main
worktree's `doc/08_tracking/test/test_db.sdn` and `test_result.md` kept their
`2026-09-04 08:32` mtimes throughout. Per-spec runs do not rewrite the tracking
files, so the 4-way fan-out could not race on them.

## 2. Method

### 2.1 Mechanical first pass

`scripts/check/stale-status-sweep.shs` (new, this lane) buckets each row by what
its declared `reproducible_by` actually is, runs the runnable ones, and writes
one resumable result file per row containing the runner's **own** verdict line.
Bucketing of the 272 input rows:

| bucket | rows | treatment |
|---|---|---|
| `RUN` — declared repro is a spec/script on disk | 95 | executed |
| `RUN-DERIVED` — DB says `NONE`, but the bug RECORD names a `_spec.spl` that exists | 47 | executed, tagged weak |
| `RUN-DERIVED-SHS` — DB says `NONE`, record names an existing `scripts/check/*.shs` | 13 | executed, tagged weak |
| `MANUAL-NONE` — `NONE`, and the record names nothing runnable | 94 | not runnable |
| `SPEC-MISSING` — a repro is named but absent from disk | 7 | not runnable |
| `MANUAL-BOOTSTRAP` — repro is `scripts/bootstrap/bootstrap-from-scratch.sh` | 5 | deliberately NOT run (hours long; a bootstrap is already running on this host) |
| `MANUAL-DOC` / `MANUAL-SOURCE` / `MANUAL-HEAVY` / `MANUAL-OTHER` | 11 | repro is a doc, a log, a source file, a `.py`, a `.c`, or a seed/bootstrap-class guard |

**155 of 272 rows (57%) were actually executed.** The remaining 117 were not
tested and no verdict is claimed for any of them.

### 2.2 The lane trap, measured rather than assumed

CLAUDE.md warns that the test runner exports
`SIMPLE_EXECUTION_MODE=interpret`. That is confirmed in source
(`src/app/test_runner_new/test_runner_single.spl:1089-1090`,
`src/lib/nogc_sync_mut/test_runner/test_runner_single.spl:169-170`,
`src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl:213`) and, more to the
point, **measured**. A probe spec that simply prints its own environment:

```
$ bin/simple test build/sweep/lane_probe_spec.spl
LANE_PROBE exec_mode=interpret runtime_mode=interpreter
SPEC FILE VERDICT: build/sweep/lane_probe_spec.spl outcome=OK declared>=1 executed=1 passed=1 failed=0 skipped=0 dropped=0

$ bin/simple run build/sweep/lane_probe_spec.spl
LANE_PROBE exec_mode= runtime_mode=
SPEC FILE VERDICT: build/sweep/lane_probe_spec.spl outcome=OK declared>=1 executed=1 passed=1 failed=0 skipped=0 dropped=0
```

An independent corroboration sits in the tree already —
`test/01_unit/compiler/class_reference_semantics_spec.spl`'s header states that
"under `bin/simple test` every field/array store VALUE-COPIES the class
instance ... Under the default JIT (`bin/simple run`) all cases alias correctly".

Consequence: the original LANE-SUSPECT rule (codegen-class **and** the spec
shells out) was too narrow. **Every** spec body runs interpreted under
`bin/simple test`, shell-out or not, so no codegen/JIT/native row can be
certified by a green `test` run alone. The rule was widened accordingly, and a
**second lane was added**: `bin/simple run <spec>` executes the same describe
blocks and emits the same verdict line in the seed's default JIT lane. Every
codegen-class LANE-SUSPECT row was re-run there.

Rows tagged `stage-lane` (21 of them — `stage1`..`stage4`, `bootstrap`,
`selfhost`) are excluded from that upgrade on purpose: reproducing them needs a
deployed pure-Simple self-hosted binary, which this host does not have. **No
lane available here can certify a stage row.**

Still untested by any lane on this host: **native / AOT** (`compile --native`)
and the **pure-Simple `native-build`** lane. `DUAL-LANE-GREEN` below means
interpret + JIT, and nothing more.

### 2.3 Two false-verdict classes caught mechanically

- **Inversion-pinning specs.** Some specs deliberately assert the *wrong*,
  currently-observed value so a defect stays executable and loud
  ("PINS CURRENT BEHAVIOR", "divergence pinned", "asserts the WRONG"). A GREEN
  run on one of those means the bug is **still present**. Detected by grep and
  reclassified `STILL-BROKEN` with lane flag `pin-inverted-green`. This is what
  caught `class_field_reference_semantics_diverge_2026-08-06`, whose
  `outcome=OK declared>=6 executed=6 passed=6 failed=0` reads like a fix and is
  the opposite. The mirror case — a pin-inverted spec that now *fails* — is
  `PIN-FLIPPED` (fix candidate needing its assertions inverted); no row landed
  there in this sweep.
- **Rotted specs.** A verdict carrying `reason=parse-error` or `executed=0` is
  evidence in neither direction and is classified `SPEC-ROTTED`, not
  `STILL-BROKEN`. Two rows landed there.

### 2.4 Confidence tiers — record-derived is a hypothesis, not a repro

60 of the 155 executed rows had `reproducible_by: NONE` in the DB and were run
against a spec found by grepping the bug RECORD. That spec is often just a spec
that *observed* the bug, not one that covers it. Confirmed examples from this
run: `compiler_cross_module_private_symbol_collision_2026-06-16` resolved to
`test/01_unit/os/tls13/server_accept_spec.spl`;
`docs_titled_commit_2313821fd77_reverted_five_landed_fixes_2026-08-10` (a VCS
incident record covering five separate fixes) resolved to a single
`run_semantic_error_exit_code_spec.spl`.

**Rule applied throughout: no status-change recommendation rests on a
record-derived row without a hand check.**

---

## 3. Results — 155 of 272 rows reached

| class | rows | meaning |
|---|---:|---|
| `STILL-BROKEN` | 79 | the spec ran and failed (or is pin-inverted and green) |
| `LIKELY-FIXED` | 30 | spec ran clean, non-codegen row, right lane |
| `DUAL-LANE-GREEN` | 17 | codegen row, clean in BOTH the interpret and JIT lanes; native/AOT untested |
| `LANE-SUSPECT` | 10 | passed, but only in a lane that cannot contain the defect (all `stage-lane`) |
| `NO-EVIDENCE` | 10 | the runner explicitly refused to certify, or executed nothing |
| `TIMEOUT` | 7 | killed at 420 s |
| `SPEC-ROTTED` | 2 | parse error / zero examples executed |
| — reached subtotal — | **155** | |
| `NO-REPRO` | 110 | nothing runnable on this host |
| `SPEC-MISSING` | 7 | named repro absent from disk |
| — not reached subtotal — | **117** | |
| **total** | **272** | |

**The 8-in-15 optimistic-drift ratio does NOT hold at this scale.** Among the
155 rows actually reached, 47 (30%) are fixed-candidates (`LIKELY-FIXED` +
`DUAL-LANE-GREEN`) and 79 (51%) are confirmed still failing. Of the 47
candidates, hand verification (§4) disqualified a large fraction — the honest
clean-close shortlist is **6 rows**, not 47. Extrapolating the 8/15 ratio to
272 rows would have overstated the free wins by roughly an order of magnitude.

The full 272-row classified table, one row per input row with the verbatim
verdict line, is at the end of this report (§7).

### 3.1 Notable non-reached rows

Both **P0** rows are unreachable here and neither was tested:

- `stage3_current_source_hir_rss_termination_2026_08_14` — repro is
  `build/native_probe/stage3-fresh/build-cycle3.log`, which does not exist on
  disk (`SPEC-MISSING`).
- `stage2_struct_field_offset_model_mismatch_oob_read_2026-08-30` — repro is its
  own bug record (`MANUAL-DOC`), and it is a `stage-lane` row besides.

Seven rows timed out at 420 s and are unresolved:
`ast_env_mirror_bypasses_stale_index_guard_2026-08-01`,
`ecc_p384_p521_sign_verify_broken_2026-07-20`,
`jit_i64_boundary_constant_wraps_to_negative_2026-08-09`,
`riscv_cross_target_nil_receiver_phase3_hir_2026-07-24`,
`self_hosted_cli_native_build_silent_no_artifact_2026-08-14`,
`selfhost_native_build_const_eval_mapnew_body_on_string_2026-07-17`,
`cranelift_unannotated_module_bool_global_tagbox_truthy_2026-07-27`.

Two rows are `SPEC-ROTTED` — their named repro no longer parses or executes
nothing, which is a tracking defect in its own right:
`text_len_bytes_vs_index_codepoints_2026-07-02` and
`web_renderer_layout_paint_hang_resolution_independent_2026-07-14`.

---

## 4. Hand verification

18 fixed-candidates were read by hand: the bug record's stated defect against
the example names of the spec that actually ran. **12 of the 18 do not survive
the check.** The pattern that kills them is uniform — the spec is green, and it
is green about something adjacent to the defect.

### 4.1 Survives — recommend a status change (6)

| # | Row | Verdict line as printed | Why it holds |
|---|---|---|---|
| 1 | `elf_parser_relocations_merged_without_target_section_2026-08-08` | `SPEC FILE VERDICT: test/01_unit/compiler/backend/linker/elf_reloc_target_section_spec.spl outcome=OK declared>=4 executed=4 passed=4 failed=0 skipped=0 dropped=0` | The record's own body says `Status: RESOLVED 2026-08-17 (fix + reproducing spec + class-detection spec landed)` and names the root cause (`sh_info` unparsed at ELF64 shdr offset 44). The spec's four examples are exactly the defect: *records `sh_info` on each RELA section header*, *attributes every merged relocation to the section it applies to*, *keeps `target_section_idx` consistent*. Also green in the JIT lane. **The record and the DB disagree; the record is right.** |
| 2 | `interpreter_bare_arg_not_some_wrapped_at_optional_param_2026-08-04` | `SPEC FILE VERDICT: test/01_unit/language/dict_get_option_match_spec.spl outcome=OK declared>=2 executed=2 passed=2 failed=0 skipped=0 dropped=0` | Record body: `Status: FIXED 2026-08-05 in src/compiler_rust/compiler/src/interpreter_patterns.rs (the Pattern::Enum arm)`. The record also states `Engines: interpreter only. The JIT was already correct.` — so the interpret lane IS the defect's lane and this run is on-lane. Examples *matches Some(x) for a present key* / *falls through to else for a missing key* are the reported symptom. |
| 3 | `struct_shorthand_arg_order_binds_wrong_field_2026-07-20` | `SPEC FILE VERDICT: test/feature/usage/struct_shorthand_spec.spl outcome=OK declared>=15 executed=15 passed=15 failed=0 skipped=0 dropped=0` | The record quotes the two failing examples by name, and both — *uses explicit then shorthand*, *mixes shorthand with explicit named argument* — are in this spec and now pass. Declared repro, right lane (record localises the defect to "interpreter or HIR lowering"). |
| 4 | `x25519_extern_not_registered_interp_2026-06-15` | `SPEC FILE VERDICT: test/01_unit/lib/common/crypto/typed/asym_spec.spl outcome=OK declared>=13 executed=13 passed=13 failed=0 skipped=0 dropped=0` | Record: `Status: Source fixed 2026-07-15; existing KAT and standalone run verification pending`. This run IS that pending verification — *shared secret hex matches oracle*, *shared secret len is 32* are x25519 KAT examples and pass. Note the record says **P3**, while the DB row says P1; the severity should be reconciled too. |
| 5 | `aes128_ccm_rfc3610_kat_mismatch_2026-07-20` | `SPEC FILE VERDICT: test/unit/lib/crypto/aes128_ccm_rfc3610_kat_spec.spl outcome=OK declared>=12 executed=12 passed=12 failed=0 skipped=0 dropped=0` | The record names this exact spec as the exercising surface and the symptom is RFC 3610 §8 KAT mismatch on vectors #1/#4/#7. All three vectors' encrypt+decrypt examples pass, plus tamper-rejection. The record's instruction "**Do not touch the expected vectors**" is satisfied — the spec still asserts the canonical RFC values. |
| 6 | `engine2d_factory_returns_dict_under_test_runner_2026-08-19` | `SPEC FILE VERDICT: test/02_integration/rendering/engine2d_drawing_spec.spl outcome=OK declared>=2 executed=2 passed=2 failed=0 skipped=0 dropped=0` | The defect is defined as happening **under `bin/simple test`** ("`Engine2D.create_with_backend(...)` returns a dict"), so the interpret lane is the correct and only relevant lane. *draw_rect_filled fills correct region* and *clear fills entire framebuffer* both require a real Engine2D, not a dict. Record-derived, but the lane and the mechanism line up exactly. **Weakest of the six** — the spec does not name the bug id. |

### 4.2 Fails the check — a green spec that does not cover the defect (12)

| # | Row | Verdict line as printed | Why the pass is not a fix |
|---|---|---|---|
| 7 | `enum_bare_name_collision_registry_2026-08-01` | `... enum_bare_name_collision_loud_miss_spec.spl outcome=OK declared>=14 executed=14 passed=14 failed=0 ...` | Record: `ENUMERATION LANDED — no fix applied. Needs an owner decision on the resolution strategy before any code change`. The spec tests the *loud-miss diagnostic* that the enumeration lane built; the underlying silent wrong-arm selection across module boundaries is untouched. Textbook adjacent-coverage. |
| 8 | `interp_expect_to_equal_swallows_failures_multi_describe_2026-06-15` | `... compress/typed/types_spec.spl outcome=OK declared>=23 ...` | The defect is *`expect().to_equal()` reports PASS on a wrong value in a multi-describe spec*. A green run is precisely what the bug produces, so it distinguishes nothing. The spec's positive control (*1+1==2 proves runner fires assertions*) does not help; only a **negative** control — an assertion that must fail — would. Zero evidence either way. |
| 9 | `interpreter_module_array_stale_read_via_free_fn_helper_2026-07-29` | `... nogc_async_mut/async_spec.spl outcome=OK ...` | Record: `open (worked around in src/lib/nogc_async_mut/async/cancellation.spl; root cause is in the interpreter, not fixable from pure Simple stdlib code)`. The green example *CancellationToken works* exercises the workaround, not the interpreter root cause. |
| 10 | `indexed_char_to_i64_silent_zero_family_2026-08-10` | `PASS — 596 site(s) scanned, 0 string-indexed hits, control hit OK` | The repro is a **census ratchet**, not a behavioural test: it proves no call sites of the pattern remain, not that `s[i].to_i64()` returns the right value. Record also carries `CLAIMED-OFFHOST 2026-08-17 — do not work locally` and `Status re-verified 2026-08-17 by source inspection`. |
| 11 | `host_vulkan_lavapipe_graphics_entry_points_stubbed_without_vulkan_feature_2026-08-11` | `... host_vulkan_lavapipe_compare_spec.spl outcome=OK ...` | The defect is that **every graphics entry point** (`rt_vulkan_create_offscreen_render_pass` etc.) is a 0-returning stub. The spec's two examples are *reaches a real software Vulkan device* and *reports unavailable when the pinned ICD does not exist* — device enumeration, which the record explicitly says already works. The broken half is not covered at all. |
| 12 | `gc_analysis_desugar_dropped_method_bodies_2026-08-02` | `... semantics/gc_roots_barriers_spec.spl outcome=OK declared>=39 ...` | Record: roots/barriers "are now executable and covered ... `mod.spl` is still broken, and **41 of the other 45** `(was: impl ...)` deleted blocks tree-wide are unfixed". The spec covers the fixed sliver. Partially fixed; the row should be narrowed, not closed. |
| 13 | `class_field_reference_semantics_diverge_2026-08-06` | `... class_reference_semantics_spec.spl outcome=OK declared>=6 executed=6 passed=6 failed=0 ...` | **Inversion-pinned.** The spec's header: "every example marked TODO(class-identity-contract) asserts the WRONG (value-copy) result on purpose ... When reference semantics are fixed, these examples flip red." Green means the divergence is still live. Caught mechanically, not by eye. |
| 14 | `duplicate_public_symbols_differing_return_types_jit_misdispatch_2026-08-09` | `... cache/action_key_spec.spl outcome=OK declared>=32 executed=32 passed=32 failed=0 ...` (green in the JIT lane too) | The defect is not the spec's assertions — it is the collision warnings that spec run emits. **Measured in this sweep's own log: 22 `compiler_cross_module_private_symbol_collision` warnings still fire** during that green run. Improved from the record's 373, but not gone. The record's scale figure is stale and should be updated to 22. |
| 15 | `array_at_returns_nil_for_every_index_2026-08-01` | `... array_at_option_spec.spl outcome=OK declared>=11 executed=11 passed=11 failed=0 ...` (green in the JIT lane too) | Record's own lane table: interpreter FIXED, JIT FIXED, native LLVM FIXED to JIT parity — "**The pure-Simple `native-build` lane is still OPEN** (no `at` arm in its MIR lowering)". Exactly the lane no harness on this host can reach. Narrow the row to `native-build`; do not close. |
| 16 | `dict_class_field_contains_key_after_insert_2026-08-08` | `... dict_class_field_contains_key_after_insert_spec.spl outcome=OK declared>=3 executed=3 passed=3 failed=0 ...` | The spec's own third example is titled *"...(interpreter-only; **native SEGFAULTs**, see bug doc)"*. The interpreter half is genuinely fixed; the native half is still a segfault by the spec's own admission. Split, do not close. |
| 17 | `enum_impl_static_fn_scoping_2026-07-29` | interpret: `... static_fn_spec.spl outcome=OK declared>=26 executed=26 passed=26 failed=0 ...`; JIT: same 26/26 | Genuinely encouraging — the record's stated failure lane is "silent wrong values on the default JIT engine", and the JIT lane is now 26/26. But the record is a *scoping study* with a "Why this is not a small fix" section covering more surface than this one spec. Recommend: re-scope the row against the study's own checklist, not a blanket close. |
| 18 | `interp_run_enum_single_field_payload_corrupt_2026-06-15` | JIT lane: `... bytes/bits_spec.spl outcome=OK declared>=13 executed=13 passed=13 failed=0 ...` | Defect is specifically on `bin/simple run` (JIT), and the JIT lane is now green over 13 bit-packing round-trip examples that would expose an `n >> 3` payload shift. Record-derived spec though — it does not name the bug id, and the record's minimal repro (`enum Tok: Literal(b: i64)`) is not directly present. Promising; needs the minimal repro run before closing. |

---

## 5. Recommended status changes

### 5.1 Close (6) — `open` -> `fixed`

Every one of these has BOTH a clean on-lane verdict line quoted in §4.1 AND a
bug record whose own text supports the change.

1. `elf_parser_relocations_merged_without_target_section_2026-08-08`
2. `interpreter_bare_arg_not_some_wrapped_at_optional_param_2026-08-04`
3. `struct_shorthand_arg_order_binds_wrong_field_2026-07-20`
4. `x25519_extern_not_registered_interp_2026-06-15` (**also reconcile severity**: the record says P3, the DB row says P1)
5. `aes128_ccm_rfc3610_kat_mismatch_2026-07-20`
6. `engine2d_factory_returns_dict_under_test_runner_2026-08-19`

### 5.2 Narrow the scope, keep open (4)

The row's headline defect is fixed in the lane that was tested; a named,
still-broken remainder justifies keeping it open under a tighter title.

| Row | Remaining scope |
|---|---|
| `array_at_returns_nil_for_every_index_2026-08-01` | pure-Simple `native-build` lane only (no `at` arm in its MIR lowering) |
| `dict_class_field_contains_key_after_insert_2026-08-08` | native lane only (segfault, per the spec's own example title) |
| `gc_analysis_desugar_dropped_method_bodies_2026-08-02` | `mod.spl` + the 41 of 45 unfixed `(was: impl ...)` blocks |
| `duplicate_public_symbols_differing_return_types_jit_misdispatch_2026-08-09` | still live; **update the measured scale from 373 to 22** collisions |

### 5.3 Rows that are worse than recorded (3)

| Row | Recorded | Measured today |
|---|---|---|
| `class_field_reference_semantics_diverge_2026-08-06` | open | Confirmed still diverging — its pinning spec is green, which is the failure signal. No drift, but the row deserves a note that its spec reads inverted. |
| `text_len_bytes_vs_index_codepoints_2026-07-02` | open, with a named repro | `SPEC-ROTTED` — the named repro no longer parses or executes zero examples. The row has lost its evidence. |
| `web_renderer_layout_paint_hang_resolution_independent_2026-07-14` | open, with a named repro | `SPEC-ROTTED`, same failure. |

### 5.4 Tracking-hygiene changes, no engineering (2 classes)

- **7 rows name a repro that is not on disk** (`SPEC-MISSING`), including the P0
  `stage3_current_source_hir_rss_termination_2026_08_14` (points at
  `build/native_probe/stage3-fresh/build-cycle3.log`, a path under a gitignored
  `build/` tree). Three more have prose pasted into the `reproducible_by`
  column instead of a path (`interp_qualified_enum_is_payload_variant`,
  `md_diag_tuple_element_corruption`, `md_slugify_string_corruption`). These
  rows cannot be verified by anyone until the field is repaired.
- **154 of 272 rows carry `reproducible_by: NONE`.** 60 of those had a usable
  spec sitting in their own bug record, which the DB simply never captured.
  Backfilling `reproducible_by` from the record would raise mechanical coverage
  from 57% to well over 70% at zero engineering cost.

### 5.5 How to apply these — the sanctioned path is currently unavailable

`doc/08_tracking/bug/bug_db.sdn` opens with two `#sdn-crc32:` header lines, so
it must not be hand-edited. The sanctioned CLI exists:

- `simple bug-add` (`src/app/cli/dispatch/table.spl:639` ->
  `src/app/bug_add/main.spl`) — **adds** a row. Its flags are
  `--id/--severity/--title/--file/--line/--repro/--date`. It has **no
  `--status`**, so it cannot apply any change in this report.
- `simple bug-resolve` (`table.spl:653` -> `src/app/bug_resolve/main.spl`) —
  "Mark a bug as Closed in the bug database". This IS the sanctioned path for
  §5.1. It requires `--id`, `--date`, a full token receipt
  (`--input-tokens`/`--output-tokens`/`--cache-read-tokens`/`--cache-create-tokens`/`--token-source`/`--token-provider`)
  and `--knowledge=<path|none>`.
- There is **no** sanctioned CLI for §5.2/§5.3 (re-scope, re-title, severity
  reconcile). Only add and close exist.

Neither command runs on this host:

```
$ bin/simple bug-resolve --help
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
error: file not found: bug-resolve
```

`bin/simple` is the Rust seed, and the seed dispatches neither `bug-add` nor
`bug-resolve`. **Applying any status change in this report therefore requires a
deployed pure-Simple self-hosted binary** — which is itself the subject of open
row `no_self_hosted_binary_deployed_blocks_bootstrap_gate_2026-08-09`. That is a
finding, not a blocker for this report: the recommendations stand and can be
applied the moment a self-hosted binary is deployed. `bug-gen` was deliberately
NOT run, since it regenerates tracking files.

---

## 6. Reproducing this sweep

```bash
sh scripts/check/stale-status-sweep.shs plan /tmp/tri/pkg/stale_candidates_p01.txt
SWEEP_JOBS=4 SWEEP_TIMEOUT=420 sh scripts/check/stale-status-sweep.shs run
SWEEP_JOBS=4 SWEEP_TIMEOUT=420 sh scripts/check/stale-status-sweep.shs jit
sh scripts/check/stale-status-classify.shs > build/sweep/classified.txt
```

Both scripts write only under `build/sweep/` (per-row result files make the run
resumable; full per-row logs are kept at `build/sweep/log/<id>.log`). Neither is
wired into any gate, and neither mutates a bug row, spec, TODO or feature.
Note that `build/` is gitignored (`.gitignore:106`), so the raw result files are
NOT committed — §7 below is the durable copy.

---

## 7. Full classified table (all 272 rows)

Columns: severity, bug id, class, evidence tier (`declared` = the DB's own
`reproducible_by`; `record-derived` = a spec found in the bug record because the
DB said `NONE`), lane flag, and the verdict line exactly as the runner printed
it. `n/a` in the evidence column means the row was never executed.

| Sev | Bug id | Class | Evidence | Lane flag | Verdict line as printed |
|-----|--------|-------|----------|-----------|-------------------------|
| P0 | `stage2_struct_field_offset_model_mismatch_oob_read_2026-08-30` | **NO-REPRO** | n/a | stage-lane | `not runnable on this host: doc/08_tracking/bug/stage2_struct_field_offset_model_mismatch_oob_read_2026-08-30.md` |
| P0 | `stage3_current_source_hir_rss_termination_2026_08_14` | **SPEC-MISSING** | n/a | stage-lane | `named repro absent from disk: build/native_probe/stage3-fresh/build-cycle3.log` |
| P1 | `array_at_returns_nil_for_every_index_2026-08-01` | **DUAL-LANE-GREEN** | record-derived | codegen-shellout | `SPEC FILE VERDICT: test/01_unit/lib/common/array_at_option_spec.spl outcome=OK declared>=11 executed=11 passed=11 failed=0 skipped=0 dropped=0  ||JIT|| SPEC FILE VERDICT: test/01_unit/lib/common/array` |
| P1 | `dict_array_contains_raw_untagged_key_2026-08-02` | **DUAL-LANE-GREEN** | record-derived | codegen-shellout | `SPEC FILE VERDICT: test/01_unit/compiler/dict_array_membership_tagged_key_spec.spl outcome=OK declared>=7 executed=7 passed=7 failed=0 skipped=0 dropped=0  ||JIT|| SPEC FILE VERDICT: test/01_unit/comp` |
| P1 | `duplicate_public_symbols_differing_return_types_jit_misdispatch_2026-08-09` | **DUAL-LANE-GREEN** | declared | codegen-shellout | `SPEC FILE VERDICT: test/01_unit/compiler/cache/action_key_spec.spl outcome=OK declared>=32 executed=32 passed=32 failed=0 skipped=0 dropped=0  ||JIT|| SPEC FILE VERDICT: test/01_unit/compiler/cache/ac` |
| P1 | `elf_parser_relocations_merged_without_target_section_2026-08-08` | **DUAL-LANE-GREEN** | record-derived | codegen-shellout | `SPEC FILE VERDICT: test/01_unit/compiler/backend/linker/elf_reloc_target_section_spec.spl outcome=OK declared>=4 executed=4 passed=4 failed=0 skipped=0 dropped=0  ||JIT|| SPEC FILE VERDICT: test/01_un` |
| P1 | `enum_associated_fn_never_called_on_jit_2026-07-28` | **DUAL-LANE-GREEN** | declared | codegen-interpret-lane | `SPEC FILE VERDICT: test/shared/control_flow/static_fn_spec.spl outcome=OK declared>=26 executed=26 passed=26 failed=0 skipped=0 dropped=0  ||JIT|| SPEC FILE VERDICT: test/shared/control_flow/static_fn` |
| P1 | `enum_impl_static_fn_scoping_2026-07-29` | **DUAL-LANE-GREEN** | declared | codegen-interpret-lane | `SPEC FILE VERDICT: test/shared/control_flow/static_fn_spec.spl outcome=OK declared>=26 executed=26 passed=26 failed=0 skipped=0 dropped=0  ||JIT|| SPEC FILE VERDICT: test/shared/control_flow/static_fn` |
| P1 | `interp_index_of_digit_leading_literal_2026-07-22` | **DUAL-LANE-GREEN** | declared | codegen-shellout | `SPEC FILE VERDICT: test/01_unit/language/option_i64_value3_sentinel_spec.spl outcome=OK declared>=5 executed=5 passed=5 failed=0 skipped=0 dropped=0  ||JIT|| SPEC FILE VERDICT: test/01_unit/language/o` |
| P1 | `interp_run_enum_single_field_payload_corrupt_2026-06-15` | **DUAL-LANE-GREEN** | declared | codegen-interpret-lane | `SPEC FILE VERDICT: test/01_unit/lib/common/bytes/bits_spec.spl outcome=OK declared>=13 executed=13 passed=13 failed=0 skipped=0 dropped=0  ||JIT|| SPEC FILE VERDICT: test/01_unit/lib/common/bytes/bits` |
| P1 | `interp_static_fn_new_hijacks_named_ctor_2026-07-02` | **DUAL-LANE-GREEN** | declared | codegen-shellout | `SPEC FILE VERDICT: test/03_system/feature/usage/named_ctor_with_static_new_spec.spl outcome=OK declared>=4 executed=4 passed=4 failed=0 skipped=0 dropped=0  ||JIT|| SPEC FILE VERDICT: test/03_system/f` |
| P1 | `jit_array_element_i64_storage_truncation_2026-08-17` | **DUAL-LANE-GREEN** | record-derived | codegen-shellout | `SPEC FILE VERDICT: test/03_system/compiler/i64_interpolation_engine_parity_spec.spl outcome=OK declared>=7 executed=7 passed=7 failed=0 skipped=0 dropped=0  ||JIT|| SPEC FILE VERDICT: test/03_system/c` |
| P1 | `jit_game2d_backend_method_dispatch_sigsegv_2026-07-02` | **DUAL-LANE-GREEN** | declared | codegen-shellout | `SPEC FILE VERDICT: test/03_system/game2d/breakout_production_spec.spl outcome=OK declared>=1 executed=1 passed=1 failed=0 skipped=0 dropped=0  ||JIT|| SPEC FILE VERDICT: test/03_system/game2d/breakout` |
| P1 | `jit_hex_to_u8_array_byte_corruption_2026-06-30` | **DUAL-LANE-GREEN** | declared | codegen-interpret-lane | `SPEC FILE VERDICT: test/01_unit/lib/common/cert/x509_spec.spl outcome=OK declared>=21 executed=21 passed=21 failed=0 skipped=0 dropped=0  ||JIT|| SPEC FILE VERDICT: test/01_unit/lib/common/cert/x509_s` |
| P1 | `jit_substring_chained_to_int_returns_pointer_2026-08-04` | **DUAL-LANE-GREEN** | record-derived | codegen-shellout | `SPEC FILE VERDICT: test/01_unit/language/text_chained_method_to_int_repro_spec.spl outcome=OK declared>=3 executed=3 passed=3 failed=0 skipped=0 dropped=0  ||JIT|| SPEC FILE VERDICT: test/01_unit/lang` |
| P1 | `me_method_mutation_through_optional_binding_discarded_2026-08-04` | **DUAL-LANE-GREEN** | record-derived | codegen-shellout | `SPEC FILE VERDICT: test/01_unit/compiler/lint/option_me_call_spec.spl outcome=OK declared>=15 executed=15 passed=15 failed=0 skipped=0 dropped=0  ||JIT|| SPEC FILE VERDICT: test/01_unit/compiler/lint/` |
| P1 | `sspec_expect_eq_to_equal_false_silently_wrong_2026-07-17` | **DUAL-LANE-GREEN** | declared | codegen-interpret-lane | `SPEC FILE VERDICT: test/01_unit/compiler/interpreter/logical_short_circuit_spec.spl outcome=OK declared>=3 executed=3 passed=3 failed=0 skipped=0 dropped=0  ||JIT|| SPEC FILE VERDICT: test/01_unit/com` |
| P1 | `tag_boxing_value_corruption_family_triage_2026-08-01` | **DUAL-LANE-GREEN** | record-derived | codegen-shellout | `SPEC FILE VERDICT: test/01_unit/language/any_erased_bool_to_text_spec.spl outcome=OK declared>=3 executed=3 passed=3 failed=0 skipped=0 dropped=0  ||JIT|| SPEC FILE VERDICT: test/01_unit/language/any_` |
| P1 | `verification_std_cross_module_type_name_collision_2026-08-17` | **DUAL-LANE-GREEN** | declared | codegen-interpret-lane | `SPEC FILE VERDICT: test/00_formal_verification/compiler/unified_attrs_spec.spl outcome=OK declared>=6 executed=6 passed=6 failed=0 skipped=0 dropped=0  ||JIT|| SPEC FILE VERDICT: test/00_formal_verifi` |
| P1 | `build11_stage3_compile_context_corruption_2026-08-14` | **LANE-SUSPECT** | declared | stage-lane | `stage3_context_tuple_return_direct_count=1 stage3_context_tuple_return_getter_count=1 stage3_context_tuple_return_status=pass ` |
| P1 | `interp_run_cross_module_db_option_mutation_2026-06-13` | **LANE-SUSPECT** | declared | codegen-shellout | `db_bench_driver: wrote report -> doc/09_report/perf/perf_baseline_db_2026-06-13.md db_bench_driver: updated metrics -> doc/10_metrics/perf/perf_baseline_db_table.md Done. Both docs written. ` |
| P1 | `pure_simple_untyped_list_element_read_unconditional_int_decode_segv_2026-08-08` | **LANE-SUSPECT** | declared | codegen-shellout | `PASS — interpreter reference lane correct: typed=[5,7], list-param=[5,7]` |
| P1 | `selfhost_two_hop_field_method_mutation_lost_2026-07-27` | **LANE-SUSPECT** | declared | stage-lane | `SPEC FILE VERDICT: test/01_unit/compiler/two_hop_field_method_mutation_spec.spl outcome=OK declared>=5 executed=5 passed=5 failed=0 skipped=0 dropped=0` |
| P1 | `stage3_numeric_interpolation_slot_corruption_2026-08-13` | **LANE-SUSPECT** | record-derived | stage-lane | `SPEC FILE VERDICT: test/01_unit/compiler/interpreter/pure_simple_interpolation_literal_segments_spec.spl outcome=OK declared>=4 executed=4 passed=4 failed=0 skipped=0 dropped=0` |
| P1 | `stage3_selfhost_phase3_error_array_index_after_struct_reassign_silently_noops_2026-08-10` | **LANE-SUSPECT** | record-derived | stage-lane | `SPEC FILE VERDICT: test/01_unit/compiler/driver/ctx_error_array_index_after_reassign_spec.spl outcome=OK declared>=3 executed=3 passed=3 failed=0 skipped=0 dropped=0` |
| P1 | `stage3_selfhost_post_hir_segfault_2026-08-14` | **LANE-SUSPECT** | declared | stage-lane | `SPEC FILE VERDICT: test/02_integration/compiler/stage3_aggregate_receiver_spec.spl outcome=OK declared>=2 executed=2 passed=2 failed=0 skipped=0 dropped=0` |
| P1 | `stage3_symboltable_lookup_ud2_field_access_nil_receiver_2026-08-06` | **LANE-SUSPECT** | declared | stage-lane | `SPEC FILE VERDICT: test/01_unit/compiler/hir/symbol_table_lookup_scope_guard_spec.spl outcome=OK declared>=5 executed=5 passed=5 failed=0 skipped=0 dropped=0` |
| P1 | `stage4_test_runner_pipe_capture_truncation_rt_fork_2026-07-20` | **LANE-SUSPECT** | record-derived | stage-lane | `SPEC FILE VERDICT: test/01_unit/app/arch_check_spec.spl outcome=OK declared>=74 executed=74 passed=74 failed=0 skipped=0 dropped=0` |
| P1 | `try_operator_on_option_no_early_return_2026-08-08` | **LANE-SUSPECT** | declared | codegen-shellout | `PASS — 3 engine(s) checked: default,interpret,jit —  ?  early-returns Err with the original payload` |
| P1 | `aes128_ccm_rfc3610_kat_mismatch_2026-07-20` | **LIKELY-FIXED** | declared | - | `SPEC FILE VERDICT: test/unit/lib/crypto/aes128_ccm_rfc3610_kat_spec.spl outcome=OK declared>=12 executed=12 passed=12 failed=0 skipped=0 dropped=0` |
| P1 | `aliased_array_mut_param_mutation_lost_interpreter_2026-08-06` | **LIKELY-FIXED** | record-derived | - | `SPEC FILE VERDICT: test/01_unit/compiler/interpreter/aliased_param_writeback_spec.spl outcome=OK declared>=4 executed=4 passed=4 failed=0 skipped=0 dropped=0` |
| P1 | `dict_class_field_contains_key_after_insert_2026-08-08` | **LIKELY-FIXED** | record-derived | - | `SPEC FILE VERDICT: test/01_unit/compiler/dict_class_field_contains_key_after_insert_spec.spl outcome=OK declared>=3 executed=3 passed=3 failed=0 skipped=0 dropped=0` |
| P1 | `docs_titled_commit_2313821fd77_reverted_five_landed_fixes_2026-08-10` | **LIKELY-FIXED** | record-derived | - | `SPEC FILE VERDICT: test/01_unit/app/cli/run_semantic_error_exit_code_spec.spl outcome=OK declared>=4 executed=4 passed=4 failed=0 skipped=0 dropped=0` |
| P1 | `engine2d_factory_returns_dict_under_test_runner_2026-08-19` | **LIKELY-FIXED** | record-derived | - | `SPEC FILE VERDICT: test/02_integration/rendering/engine2d_drawing_spec.spl outcome=OK declared>=2 executed=2 passed=2 failed=0 skipped=0 dropped=0` |
| P1 | `enum_bare_name_collision_registry_2026-08-01` | **LIKELY-FIXED** | declared | - | `SPEC FILE VERDICT: test/01_unit/compiler/mir/enum_bare_name_collision_loud_miss_spec.spl outcome=OK declared>=14 executed=14 passed=14 failed=0 skipped=0 dropped=0` |
| P1 | `gc_analysis_desugar_dropped_method_bodies_2026-08-02` | **LIKELY-FIXED** | record-derived | - | `SPEC FILE VERDICT: test/01_unit/compiler/semantics/gc_roots_barriers_spec.spl outcome=OK declared>=39 executed=39 passed=39 failed=0 skipped=0 dropped=0` |
| P1 | `host_toolchain_seed_pinned_lint_fmt_doccov_unrunnable_2026-07-17` | **LIKELY-FIXED** | record-derived | - | `SPEC FILE VERDICT: test/01_unit/app/io/process_limits_enforcement_spec.spl outcome=OK declared>=14 executed=14 passed=14 failed=0 skipped=0 dropped=0` |
| P1 | `indexed_char_to_i64_silent_zero_family_2026-08-10` | **LIKELY-FIXED** | declared | - | `PASS — 596 site(s) scanned, 0 string-indexed hits, control hit OK` |
| P1 | `interp_expect_to_equal_swallows_failures_multi_describe_2026-06-15` | **LIKELY-FIXED** | declared | - | `SPEC FILE VERDICT: test/01_unit/lib/common/compress/typed/types_spec.spl outcome=OK declared>=23 executed=23 passed=23 failed=0 skipped=0 dropped=0` |
| P1 | `interpreter_bare_arg_not_some_wrapped_at_optional_param_2026-08-04` | **LIKELY-FIXED** | declared | - | `SPEC FILE VERDICT: test/01_unit/language/dict_get_option_match_spec.spl outcome=OK declared>=2 executed=2 passed=2 failed=0 skipped=0 dropped=0` |
| P1 | `interpreter_module_array_stale_read_via_free_fn_helper_2026-07-29` | **LIKELY-FIXED** | declared | - | `SPEC FILE VERDICT: test/01_unit/lib/nogc_async_mut/async_spec.spl outcome=OK declared>=10 executed=10 passed=10 failed=0 skipped=0 dropped=0` |
| P1 | `jit_array_oob_read_leaks_raw_rt_nil_sentinel_2026-08-07` | **LIKELY-FIXED** | record-derived | - | `PASS — interpreter reference lane correct: miss=nil, in-bounds control=3/3, bare OOB panics` |
| P1 | `missing_cover_annotation_aborts_the_entire_system_test_run_2026-08-04` | **LIKELY-FIXED** | declared | - | `SPEC FILE VERDICT: test/03_system/stdlib/database/sdn_checksum_spec.spl outcome=OK declared>=7 executed=7 passed=7 failed=0 skipped=0 dropped=0` |
| P1 | `option_pattern_accepted_on_non_option_scrutinee_2026-07-27` | **LIKELY-FIXED** | declared | - | `SPEC FILE VERDICT: test/01_unit/compiler/interpreter/option_result_method_dispatch_spec.spl outcome=OK declared>=7 executed=7 passed=7 failed=0 skipped=0 dropped=0` |
| P1 | `ref_debug_profiler_handle_stops_aliasing_unless_tail_expression_2026-08-09` | **LIKELY-FIXED** | declared | - | `SPEC FILE VERDICT: test/01_unit/lib/debug/debug_target_ref_spec.spl outcome=OK declared>=71 executed=71 passed=71 failed=0 skipped=0 dropped=0` |
| P1 | `struct_dict_field_mutation_engine_divergence_2026-08-10` | **LIKELY-FIXED** | declared | - | `SPEC FILE VERDICT: test/01_unit/compiler/interpreter/self_field_assign_spec.spl outcome=OK declared>=13 executed=13 passed=13 failed=0 skipped=0 dropped=0` |
| P1 | `struct_shorthand_arg_order_binds_wrong_field_2026-07-20` | **LIKELY-FIXED** | declared | - | `SPEC FILE VERDICT: test/feature/usage/struct_shorthand_spec.spl outcome=OK declared>=15 executed=15 passed=15 failed=0 skipped=0 dropped=0` |
| P1 | `symbolkind_enum_match_fails_cross_module_discriminant_minus_one_2026-07-29` | **LIKELY-FIXED** | declared | - | `SPEC FILE VERDICT: test/01_unit/compiler/hir/symbol_table_id_zero_spec.spl outcome=OK declared>=3 executed=3 passed=3 failed=0 skipped=0 dropped=0` |
| P1 | `test_invocation_fixed_setup_cost_caps_every_sweep_2026-08-17` | **LIKELY-FIXED** | record-derived | - | `SPEC FILE VERDICT: test/03_system/check/test_daemon_env_override_passthrough_spec.spl outcome=OK declared>=3 executed=3 passed=3 failed=0 skipped=0 dropped=0` |
| P1 | `test_manifest_invalidation_is_size_only_mtime_never_read_2026-08-17` | **LIKELY-FIXED** | record-derived | - | `PASS — 1 invariant(s) checked, 0 violations (2 skipped for missing inputs)` |
| P1 | `test_runner_phantom_failed_after_all_examples_pass_2026-07-20` | **LIKELY-FIXED** | declared | - | `SPEC FILE VERDICT: test/02_integration/app/loader_run_function_spec.spl outcome=OK declared>=1 executed=1 passed=1 failed=0 skipped=0 dropped=0` |
| P1 | `tierless_std_import_ambiguity_resolves_by_registration_order_2026-07-29` | **LIKELY-FIXED** | declared | - | `SPEC FILE VERDICT: test/01_unit/compiler/module_resolver/tier_ambiguity_warning_spec.spl outcome=OK declared>=5 executed=5 passed=5 failed=0 skipped=0 dropped=0` |
| P1 | `to_int_optional_lies_and_some_i64_payload_shift_2026-07-27` | **LIKELY-FIXED** | record-derived | - | `SPEC FILE VERDICT: test/01_unit/lib/common/convert_fail_closed_spec.spl outcome=OK declared>=14 executed=14 passed=14 failed=0 skipped=0 dropped=0` |
| P1 | `tree_wipe_module_damage_census_2026-08-04` | **LIKELY-FIXED** | record-derived | - | `SPEC FILE VERDICT: src/app/fix/rules/impl/lint_spec.spl outcome=OK declared>=1 executed=1 passed=1 failed=0 skipped=0 dropped=0` |
| P1 | `tuple_destructuring_does_not_bind_2026-07-27` | **LIKELY-FIXED** | record-derived | - | `SPEC FILE VERDICT: test/01_unit/compiler/tuple_destructuring_spec.spl outcome=OK declared>=7 executed=7 passed=7 failed=0 skipped=0 dropped=0` |
| P1 | `u64_collections_clobber_recurrence_engine_2026-08-11` | **LIKELY-FIXED** | record-derived | - | `check-hook-installation: PASS — 12 check(s) performed, hook wiring intact push-must-check: PASS — 0 refs to push (no-op) ` |
| P1 | `untyped_list_element_read_seed_rootcause_2026-07-30` | **LIKELY-FIXED** | record-derived | - | `PASS — interpreter reference lane correct: typed=[5,7], list-param=[5,7]` |
| P1 | `wildcard_std_spec_import_drops_expect_not_2026-08-04` | **LIKELY-FIXED** | record-derived | - | `SPEC FILE VERDICT: test/01_unit/lib/gc_async_mut/processing/metal_fill_u32_identity_spec.spl outcome=OK declared>=1 executed=1 passed=1 failed=0 skipped=0 dropped=0` |
| P1 | `x25519_extern_not_registered_interp_2026-06-15` | **LIKELY-FIXED** | declared | - | `SPEC FILE VERDICT: test/01_unit/lib/common/crypto/typed/asym_spec.spl outcome=OK declared>=13 executed=13 passed=13 failed=0 skipped=0 dropped=0` |
| P1 | `any_receiver_element_read_shift_and_tag_2026-08-06` | **NO-EVIDENCE** | declared | - | `warning: public function  file_read_text_at  has 2 co-compiled definitions with 2 differing signatures ((text,i64,i64)->Generic { name: "Result", args: [text, text] } vs (text,i64,i64)->Optional(text)` |
| P1 | `engine2d_simd_span_kernels_slower_and_fill_colour_corrupt_2026-08-06` | **NO-EVIDENCE** | declared | - | `KERNEL_RESULT kernel=blend ms=24 KERNEL_RESULT kernel=blit ms=0 SPAN_BENCH_DONE checksum=316643543 ` |
| P1 | `f64_self_hosted_call_result_codegen_2026-06-21` | **NO-EVIDENCE** | declared | stage-lane | `  This is NOT a pass. The f64 call-result ABI property was never exercised.   Deploy a pure-Simple self-hosted binary (bin/simple build bootstrap) or set   SIMPLE_BIN=/path/to/self-hosted/simple, then` |
| P1 | `llvm_constants_lost_ret_zero_2026_08_01` | **NO-EVIDENCE** | declared | - | ` warning: public function  file_read_text_at  has 2 co-compiled definitions with 2 differing signatures ((text,i64,i64)->Generic { name: "Result", args: [text, text] } vs (text,i64,i64)->Optional(text` |
| P1 | `native_try_op_on_option_silent_wrong_2026-07-14` | **NO-EVIDENCE** | declared | - | ` 0 0 ` |
| P1 | `portable_compute_cuda_emitter_pure_simple_segfault_2026-07-17` | **NO-EVIDENCE** | declared | - | `all_portable_compute_candidates_validated=false all_portable_compute_pins_verified=false all_portable_compute_toolchains_verified=false ` |
| P1 | `simple_runner_native_perf_hash_gap_2026-06-01` | **NO-EVIDENCE** | declared | - | `SCENE_RESULT scene=fill_1080p backend=simple_cpu_scalar frame_count=3 p50_ms=0 p95_ms=0 pixels_per_sec=1142857 draws_per_sec=450892 rss_kb=0 pixel_hash=1113616374 p50_ns=224000 mode=smoke SCENE_RESULT` |
| P1 | `stage3_selfhost_vtable_field_offset_relro_segv_2026-08-06` | **NO-EVIDENCE** | record-derived | stage-lane | `ERROR — nothing was checked (no binary given)` |
| P1 | `text_index_of_start_arg_dropped_and_error_sentinel_leak_2026-07-28` | **NO-EVIDENCE** | record-derived | - | `ERROR — nothing was checked: 1 binary(ies) examined but 0 carried Simple-compiled code (simple_syms>0), so 0 marker assertions were possible` |
| P1 | `ui_backend_isolation_gate_red_and_unreachable_2026-08-01` | **NO-EVIDENCE** | declared | - | `ui_backend_isolation_current=30 ui_backend_isolation_new=0 ui_backend_isolation_ok=true ` |
| P1 | `any_typed_closure_param_destroys_value_2026-07-28` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `ast_env_var_quadratic_parse_2026-06-13` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `base58_decode_reversed_polarity_rootcause_2026-07-29` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `bootstrap_planner_v1_unbound_authorization_2026-08-14` | **NO-REPRO** | n/a | stage-lane | `not runnable on this host: test/01_unit/scripts/bootstrap_planner_admission_bound_contract_test.shs` |
| P1 | `bootstrap_stage1_native_build_llvm_icmp_segfault_2026-07-09` | **NO-REPRO** | n/a | stage-lane | `not runnable on this host: -` |
| P1 | `bootstrap_stage2_empty_mir_bodies_2026-07-05` | **NO-REPRO** | n/a | stage-lane | `not runnable on this host: scripts/bootstrap/bootstrap-from-scratch.sh` |
| P1 | `bootstrap_stage3_module_surface_placeholder_nil_2026-08-01` | **NO-REPRO** | n/a | stage-lane | `not runnable on this host: scripts/bootstrap/bootstrap-from-scratch.sh` |
| P1 | `bootstrap_stage3_selfhost_seed_wrapper_fallback_2026-06-17` | **NO-REPRO** | n/a | stage-lane | `not runnable on this host: scripts/bootstrap/bootstrap-from-scratch.sh` |
| P1 | `bootstrap_stage4_ast_hir_overlap_memory_2026-07-27` | **NO-REPRO** | n/a | stage-lane | `not runnable on this host: scripts/bootstrap/bootstrap-from-scratch.sh` |
| P1 | `bootstrap_stage4_get_args_infinite_recursion_coredump_2026-06-21` | **NO-REPRO** | n/a | stage-lane | `not runnable on this host: scripts/bootstrap/bootstrap-from-scratch.sh` |
| P1 | `bootstrap_stage4_optional_arg_and_mixed_tail_miscompile_2026-07-23` | **NO-REPRO** | n/a | stage-lane | `not runnable on this host: -` |
| P1 | `browser_engine_free_fn_arg_mutation_lost_2026-06-30` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `bytebuffer_push_byte_freeze_wrong_interp_2026-06-15` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `cert_chain_signature_verification_missing_2026-07-17` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `chained_static_ctor_receiver_drops_mutation_2026-08-01` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `cli_driver_binary_repo_seed_infinite_delegation_loop_2026-07-25` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `codegen_rt_prefix_local_function_collision_sigsegv_2026-07-12` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `compiled_checker_parser_category_c_2026_08_03` | **NO-REPRO** | n/a | - | `not runnable on this host: scripts/check/compiled-check-tree.py` |
| P1 | `compiled_checker_transient_string_retention_2026-08-03` | **NO-REPRO** | n/a | - | `not runnable on this host: doc/08_tracking/bug/compiled_checker_multifile_rss_retention_2026-08-03.md` |
| P1 | `cranelift_direct_string_constant_null_pointer_2026-07-12` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `cranelift_noparen_method_access_miscompiles_2026-07-06` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `cranelift_u8_array_literal_data_pointer_garbage_2026-07-06` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `cross_module_imported_fn_mutation_not_propagating_2026-07-12` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `digest_hex_double_import_corruption_2026-06-15` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `dotq_existence_check_is_scalar_truthiness_on_jit_2026-07-27` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `emit_smf_stub_drops_module_content_2026-06-12` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `enum_assoc_fn_residual_exposure_2026-07-28` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `extern_return_type_mismatch_object_to_int_2026-07-21` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `freestanding_entry_module_constants_zero_stubs_2026-07-11` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `freestanding_u64_cross_fn_range_compare_miscompile` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `generator_take_returns_empty_after_name_collision_fix_2026-08-17` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `hir_lowering_quadratic_symbol_define_2026-07-28` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `hosted_string_trim_case_raw_receiver_degrades_2026-08-11` | **NO-REPRO** | n/a | - | `not runnable on this host: src/runtime/test/rt_string_trim_case_raw_receiver_selfcheck.c` |
| P1 | `interp_crossmod_local_slot_aliasing_2026-06-15` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `interp_expect_inline_equality_arg_misevaluates_2026-07-07` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `interp_logical_short_circuit_2026-07-15` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `interpreter_cross_module_enum_discriminant_3_compares_false_2026-08-04` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `interpreter_first_class_fn_dispatch_drops_nested_array_writeback_2026-08-09` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `interp_return_in_match_expr_swallowed_2026-06-30` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `interp_struct_local_copy_aliasing_2026-07-22` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `interp_testdatabase_class_collision_kills_aggregate_test_runs_2026-07-17` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `jit_corrupts_i64_array_returned_from_sha1_bytes_2026-08-04` | **NO-REPRO** | n/a | codegen-shellout | `not runnable on this host: src/lib/common/crypto/sha1.spl` |
| P1 | `jit_cross_module_tuple_field_read_returns_nil_2026-08-01` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `jit_does_not_enforce_val_block_scope_2026-08-17` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `jit_is_some_is_none_method_dispatch_gap_2026-08-17` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `jit_layout_run_full_with_ports_nil_receiver_2026-08-02` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `jit_packed_bitfield_field_read_returns_nil_2026-08-10` | **NO-REPRO** | n/a | - | `not runnable on this host: src/lib/nogc_sync_mut/driver/null_block_driver.spl` |
| P1 | `jit_swallows_undeclared_extern_and_exits_zero_2026-08-17` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `llvm_import_path_mangling_os_prefix_mismatch_2026-06-15` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `match_bare_ident_const_irrefutable_2026-07-20` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `mcp_full_program_native_codegen_and_arg_extract_2026-06-16` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `mir_lowering_codegen_error_first_call_zero_core_dump_2026-08-06` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `mutate_through_index_loses_write_2026-07-31` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `mutex_rwlock_text_value_nulled_by_pure_std_backend_2026-07-28` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `narrow_int_result_unwrap_or_returns_boxed_shift_2026-08-17` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `native_build_fabricates_weak_stub_for_unimplemented_extern_2026-08-18` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `native_class_static_ctor_missing_2026-07-23` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `native_empty_dict_text_value_sigsegv_2026-07-20` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `native_get_args_coalesce_empty_2026-07-23` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `native_mixed_tuple_field1_statement_drop_2026-07-29` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `native_nested_struct_value_copy_alias_2026-07-17` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `native_nil_receiver_crossmodule_method_scalar_return_2026-07-27` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `native_with_trait_impl_no_vtable_duck_trap_2026-07-28` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `no_self_hosted_binary_deployed_blocks_bootstrap_gate_2026-08-09` | **NO-REPRO** | n/a | stage-lane | `not runnable on this host: scripts/check/check-bootstrap-essential-tools-smoke.shs` |
| P1 | `parse_family_strips_option_jit_native_2026-08-02` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `parser_bare_trailing_neg_literal_folds_prev_line_2026-07-27` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `pure_simple_field_type_identity_keys_dispatch_2026-07-14` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `riscv64_native_entry_call_compare_codegen_2026-06-30` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `rt_vulkan_only_executes_under_classic_interpret_2026-06-17` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `rust_seed_native_bool_arg_inlined_call_wrong_value_2026-07-17` | **NO-REPRO** | n/a | codegen-shellout | `not runnable on this host: src/compiler_rust/compiler/tests/compile_and_run.rs` |
| P1 | `seed_interp_defer_lazy_imports_module_globals_2026-07-24` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `seed_interp_flat_nullable_unwrap_wrong_value_2026-07-16` | **NO-REPRO** | n/a | codegen-shellout | `not runnable on this host: scripts/check/check-native-seed-parity.shs` |
| P1 | `seed_interpreter_to_int_wrong_dispatch_2026-07-03` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `seed_jit_me_method_array_of_struct_writeback_nil_receiver_2026-07-23` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `seed_jit_spl_f64_to_bits_miscompile_2026-07-23` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `seed_jit_string_to_i64_float_tagged_silent_wrong_2026-07-28` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `seed_jit_wide_i64_literal_miscompile_2026-07-27` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `selfhost_bootstrap_unresolved_symbols_2026-06-24` | **NO-REPRO** | n/a | stage-lane | `not runnable on this host: -` |
| P1 | `set_method_route_dict_returns_nil_array_tuple_silent_noop_2026-08-02` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `simple_shared_parameter_llvm_global_load_2026-07-17` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `simple_test_runner_memory_leak_2026-06-14` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `spec_harness_module_global_mutation_via_function_invisible_2026-08-07` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `spec_runner_drops_sibling_top_level_describe_2026-06-28` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `spkc_p2_authority_publication_journal_first_use_mkdir_race_2026-08-26` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `stage3_freestanding_struct_by_value_corrupts_pmm_2026-07-11` | **NO-REPRO** | n/a | stage-lane | `not runnable on this host: -` |
| P1 | `stage3_post_folded_const_diagnostics_sigsegv_2026_08_14` | **NO-REPRO** | n/a | stage-lane | `not runnable on this host: -` |
| P1 | `stage3_selfhost_entry_module_zero_functions_2026-08-11` | **NO-REPRO** | n/a | stage-lane | `not runnable on this host: -` |
| P1 | `stage3_selfhost_nil_receiver_sigill_in_lower_expr_caller_2026-08-05` | **NO-REPRO** | n/a | stage-lane | `not runnable on this host: -` |
| P1 | `stage3_selfhost_parser_case_multielem_pattern_2026-07-17` | **NO-REPRO** | n/a | stage-lane | `not runnable on this host: -` |
| P1 | `stage4_aot_native_build_struct_field_access_sigill_2026-07-24` | **NO-REPRO** | n/a | stage-lane | `not runnable on this host: -` |
| P1 | `stage4_cranelift_direct_enum_text_cross_function_2026-07-24` | **NO-REPRO** | n/a | stage-lane | `not runnable on this host: -` |
| P1 | `stage4_cranelift_direct_origin_regression_2026-07-23` | **NO-REPRO** | n/a | stage-lane | `not runnable on this host: -` |
| P1 | `stage4_env_paths_llvm_undeclared_variables_2026_08_03` | **NO-REPRO** | n/a | stage-lane | `not runnable on this host: src/lib/nogc_async_mut/env/paths.spl` |
| P1 | `stage4_err_propagation_characterization_2026-07-04` | **NO-REPRO** | n/a | stage-lane | `not runnable on this host: -` |
| P1 | `stage4_focused_subbuild_star_import_unresolved_2026-07-27` | **NO-REPRO** | n/a | stage-lane | `not runnable on this host: -` |
| P1 | `stage4_full_cli_source_check_blank_exit8_2026-07-23` | **NO-REPRO** | n/a | stage-lane | `not runnable on this host: -` |
| P1 | `stage4_phase3_flat_ast_arena_desync_2026-08-01` | **NO-REPRO** | n/a | stage-lane | `not runnable on this host: -` |
| P1 | `stage4_selfhost_sha3_hir_infer_and_stubs_2026-06-28` | **NO-REPRO** | n/a | stage-lane | `not runnable on this host: -` |
| P1 | `std_math_abs_f64_returns_zero_2026-08-08` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `test_runner_interpreter_file_summary_greenwash_2026-07-03` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `text_starts_with_miscompiled_to_bytespan_name_collision_2026-07-27` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `threadpool_duplicate_export_collapses_type_2026-08-02` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `type_alias_declarations_discarded_at_parse_2026-07-29` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `ui_scene_route_owner_lookup_ignores_producer_scope_2026-08-08` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `unknown_field_access_no_static_error_2026-08-10` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `untyped_fn_result_erased_to_zero_2026-08-01` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `web_paint_wallclock_budget_flake_2026-07-31` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `web_showcase_vector_font_evidence_style_budget_truncation_2026-08-01` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `wm_protocol_status_event_symbols_never_implemented_2026-07-28` | **NO-REPRO** | n/a | - | `not runnable on this host: -` |
| P1 | `cranelift_native_aggregate_return_nil_receiver_hosted_wm_2026-07-26` | **SPEC-MISSING** | n/a | - | `named repro absent from disk: test/.../parent_commit_piped_result_spec.spl` |
| P1 | `interp_qualified_enum_is_payload_variant` | **SPEC-MISSING** | n/a | - | `named repro absent from disk: enum E with A(x) B; val a=E.A(x:5); (a is E.A) returns false while match a case E.A(x) binds correctly; root cause of wal_disk_replay_blank_row` |
| P1 | `md_diag_tuple_element_corruption` | **SPEC-MISSING** | n/a | - | `named repro absent from disk: for item in tuple_array: item.2 returns <value:0x..> instead of text; worked around with MdDiagLinkRef struct` |
| P1 | `md_slugify_string_corruption` | **SPEC-MISSING** | n/a | - | `named repro absent from disk: probe calling markdown_slugify with literal Alpha from different frames returns different values; worked around in md_wiki heading transclusion via exact trimmed-title co` |
| P1 | `rt_io_file_family_undefined_stubbed_silent_data_loss_2026-08-05` | **SPEC-MISSING** | n/a | - | `named repro absent from disk: test/01_unit/lib/io/file_seek_openmode_native_check.spl` |
| P1 | `seed_interp_option_match_falls_through_at_scale_2026-07-18` | **SPEC-MISSING** | n/a | - | `named repro absent from disk: test/03_system/interpreter/option_match_some_zero_regression_spec.spl` |
| P1 | `text_len_bytes_vs_index_codepoints_2026-07-02` | **SPEC-ROTTED** | record-derived | - | `SPEC FILE VERDICT: test/01_unit/lib/text/text_length_spec.spl outcome=ERROR declared>=37 executed=0 passed=0 failed=0 skipped=0 dropped=0` |
| P1 | `web_renderer_layout_paint_hang_resolution_independent_2026-07-14` | **SPEC-ROTTED** | record-derived | - | `SPEC FILE VERDICT: test/01_unit/lib/engine/font_ffi_spec.spl outcome=ERROR declared>=14 executed=0 passed=0 failed=0 skipped=0 dropped=0` |
| P1 | `aes256_ctr_keystream_wrong_after_first_block_2026-07-20` | **STILL-BROKEN** | declared | - | `SPEC FILE VERDICT: test/unit/lib/crypto/aes_ctr_nist_spec.spl outcome=ERROR declared>=4 executed=4 passed=2 failed=2 skipped=0 dropped=0` |
| P1 | `asm_template_placeholders_never_bind_2026-08-07` | **STILL-BROKEN** | record-derived | - | `SPEC FILE VERDICT: test/01_unit/compiler/frontend/flat_ast_inline_asm_bridge_spec.spl outcome=ERROR declared>=7 executed=7 passed=5 failed=2 skipped=0 dropped=0` |
| P1 | `bootstrap_stage4_selfhost_parse_memory_blowup_2026-07-20` | **STILL-BROKEN** | record-derived | stage-lane | `SPEC FILE VERDICT: test/01_unit/compiler/driver/driver_memory_lifecycle_family_spec.spl outcome=ERROR declared>=5 executed=5 passed=4 failed=1 skipped=0 dropped=0` |
| P1 | `browser_engine_css_size_quadratic_pixel_render_2026-07-04` | **STILL-BROKEN** | declared | - | `SPEC FILE VERDICT: test/01_unit/app/ui/browser_backend_pixel_paths_spec.spl outcome=ERROR declared>=9 executed=9 passed=8 failed=1 skipped=0 dropped=0` |
| P1 | `browser_layout_module_exceeds_128kib_parser_limit_2026-07-31` | **STILL-BROKEN** | declared | - | `SPEC FILE VERDICT: test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_module_split_spec.spl outcome=ERROR declared>=2 executed=2 passed=1 failed=1 skipped=0 dropped=0` |
| P1 | `browser_seccomp_denylist_and_inprocess_unjailed_2026-08-15` | **STILL-BROKEN** | record-derived | - | `SPEC FILE VERDICT: test/01_unit/lib/js/js_native_confinement_spec.spl outcome=ERROR declared>=6 executed=6 passed=2 failed=4 skipped=0 dropped=0` |
| P1 | `browser_text_node_blanks_frame_2026-08-05` | **STILL-BROKEN** | declared | - | `SPEC FILE VERDICT: test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_spec.spl outcome=ERROR declared>=130 executed=130 passed=118 failed=12 skipped=0 dropped=0` |
| P1 | `bug_sspec_daemon_optional_lookup_equality_divergence_2026-07-20` | **STILL-BROKEN** | declared | - | `SPEC FILE VERDICT: test/01_unit/lib/common/ui/draw_ir_patch_spec.spl outcome=ERROR declared>=19 executed=19 passed=17 failed=2 skipped=0 dropped=0` |
| P1 | `case_bare_ident_is_irrefutable_binding_2026-08-01` | **STILL-BROKEN** | record-derived | - | `SPEC FILE VERDICT: test/01_unit/bugs/text_ordering_cmp_spec.spl outcome=ERROR declared>=14 executed=14 passed=11 failed=3 skipped=0 dropped=0` |
| P1 | `class_field_reference_semantics_diverge_2026-08-06` | **STILL-BROKEN** | declared | pin-inverted-green | `SPEC FILE VERDICT: test/01_unit/compiler/class_reference_semantics_spec.spl outcome=OK declared>=6 executed=6 passed=6 failed=0 skipped=0 dropped=0` |
| P1 | `codegen_bare_method_receiver_type_blind_candidate_selection_2026-07-28` | **STILL-BROKEN** | declared | codegen-shellout | `SPEC FILE VERDICT: test/01_unit/compiler/codegen/erased_receiver_index_of_bind_spec.spl outcome=ERROR declared>=3 executed=3 passed=0 failed=3 skipped=0 dropped=0` |
| P1 | `compiler_cross_module_private_symbol_collision_2026-06-16` | **STILL-BROKEN** | record-derived | codegen-shellout | `SPEC FILE VERDICT: test/01_unit/os/tls13/server_accept_spec.spl outcome=ERROR declared>=32 executed=32 passed=27 failed=5 skipped=0 dropped=0` |
| P1 | `curve448_x448_scalarmult_kat_mismatch_2026-07-20` | **STILL-BROKEN** | declared | - | `SPEC FILE VERDICT: test/unit/lib/crypto/curve448_rfc7748_kat_spec.spl outcome=ERROR declared>=7 executed=7 passed=0 failed=7 skipped=0 dropped=0` |
| P1 | `declared_return_type_not_enforced_2026-08-09` | **STILL-BROKEN** | record-derived | - | `SPEC FILE VERDICT: test/01_unit/compiler/types/declared_return_type_enforced_spec.spl outcome=ERROR declared>=3 executed=3 passed=2 failed=1 skipped=0 dropped=0` |
| P1 | `ecdsa_p256_sign_verify_roundtrip_broken_2026-07-20` | **STILL-BROKEN** | declared | - | `SPEC FILE VERDICT: test/unit/lib/crypto/ecdsa_p256_spec.spl outcome=ERROR declared>=14 executed=14 passed=11 failed=3 skipped=0 dropped=0` |
| P1 | `enum_pattern_match_optional_value_silent_fallthrough_2026-07-20` | **STILL-BROKEN** | declared | - | `SPEC FILE VERDICT: test/01_unit/app/ui.browser/input_translation_spec.spl outcome=ERROR declared>=9 executed=9 passed=5 failed=4 skipped=0 dropped=0` |
| P1 | `enum_payload_dict_copied_on_function_return_2026-07-28` | **STILL-BROKEN** | declared | - | `SPEC FILE VERDICT: test/01_unit/lib/common/sdn_coverage_spec.spl outcome=ERROR declared>=71 executed=71 passed=69 failed=2 skipped=0 dropped=0` |
| P1 | `env_get_nil_coalesce_dead_fallback_2026-07-25` | **STILL-BROKEN** | declared | - | `FAIL — 1 of 5 assertion(s) failed` |
| P1 | `fault_detection_module_var_mutation_2026-06-26` | **STILL-BROKEN** | declared | - | `SPEC FILE VERDICT: test/01_unit/lib/common/fault_detection_enhanced_spec.spl outcome=ERROR declared>=19 executed=19 passed=0 failed=19 skipped=0 dropped=0` |
| P1 | `gui_8k_native_renderer_artifact_build_timeout_2026-08-13` | **STILL-BROKEN** | record-derived | - | `FAIL — AOT lane broken: native-build exit 1, binary absent` |
| P1 | `hir_package_sibling_imported_enum_surface_leak_2026_08_02` | **STILL-BROKEN** | declared | - | `[use-warning] 'module_surfaces_from_owners' is named in  use compiler.hir.hir_lowering.module_surface.{...}  but module '/home/yoon/dev/simple/.claude/worktrees/agent-a4f80fc0edf8c20ff/src/compiler/hi` |
| P1 | `hir_stmt_expr_payload_extraction_nil_2026-07-17` | **STILL-BROKEN** | record-derived | - | `SPEC FILE VERDICT: test/01_unit/compiler/hir/hir_stmt_dispatch_source_spec.spl outcome=ERROR declared>=6 executed=6 passed=2 failed=4 skipped=0 dropped=0` |
| P1 | `host_vulkan_lavapipe_graphics_entry_points_stubbed_without_vulkan_feature_2026-08-11` | **STILL-BROKEN** | record-derived | pin-inverted-green | `SPEC FILE VERDICT: test/01_unit/infra/counterpart/host_vulkan_lavapipe_compare_spec.spl outcome=OK declared>=6 executed=6 passed=6 failed=0 skipped=0 dropped=0` |
| P1 | `impl_to_free_fn_refactor_family_still_incomplete_2026-08-08` | **STILL-BROKEN** | record-derived | - | `SPEC FILE VERDICT: test/01_unit/compiler/common/impl_to_free_fn_class_a_call_sites_spec.spl outcome=ERROR declared>=7 executed=7 passed=3 failed=4 skipped=0 dropped=0` |
| P1 | `interp_f64_nested_struct_payload_zero_2026-06-14` | **STILL-BROKEN** | declared | codegen-shellout | `SPEC FILE VERDICT: test/03_system/compiler/compiler_interpret_pipeline_spec.spl outcome=ERROR declared>=6 executed=6 passed=0 failed=6 skipped=0 dropped=0` |
| P1 | `interpreter_binding_class_typed_field_snapshots_instead_of_aliasing_2026-08-10` | **STILL-BROKEN** | record-derived | codegen-shellout | `SPEC FILE VERDICT: test/02_integration/app/sj_daemon_mutual_exclusion_spec.spl outcome=ERROR declared>=5 executed=5 passed=1 failed=4 skipped=0 dropped=0` |
| P1 | `jit_class_mutation_drop_characterization_2026-07-04` | **STILL-BROKEN** | declared | codegen-shellout | `SPEC FILE VERDICT: test/03_system/interpreter/interp_value_semantics_b35_spec.spl outcome=ERROR declared>=12 executed=12 passed=10 failed=2 skipped=0 dropped=0` |
| P1 | `jit_if_nil_takes_true_branch_2026-08-04` | **STILL-BROKEN** | record-derived | codegen-shellout | `SPEC FILE VERDICT: test/01_unit/compiler/codegen/cross_engine_divergence_prevention_spec.spl outcome=ERROR declared>=5 executed=5 passed=3 failed=2 skipped=0 dropped=0` |
| P1 | `lsp_emitter_never_implemented_cli_query_2026-07-28` | **STILL-BROKEN** | record-derived | - | `src/unit/simple-lang/power/__init__.spl:9: SYMBOL: imported name  MegaWatt  is declared in no src file src/verification/simpleos_capability_rights_refinement.spl:14: SYMBOL: imported name  capability_` |
| P1 | `lsp_mcp_integer_position_args_corrupted_2026-06-14` | **STILL-BROKEN** | declared | - | `mcp_server_exists=false error=missing_mcp_server:bin/simple_mcp_server ` |
| P1 | `match_on_optional_enum_variant_falls_to_wildcard_2026-08-07` | **STILL-BROKEN** | declared | codegen-interpret-lane | `SPEC FILE VERDICT: test/01_unit/app/ui/semantic_contract_spec.spl outcome=ERROR declared>=12 executed=12 passed=8 failed=4 skipped=0 dropped=0` |
| P1 | `mir_qualified_field_key_namespace_mismatch_2026-08-08` | **STILL-BROKEN** | record-derived | codegen-interpret-lane | `SPEC FILE VERDICT: test/01_unit/compiler/mir/struct_field_order_module_qualified_spec.spl outcome=ERROR declared>=4 executed=4 passed=3 failed=1 skipped=0 dropped=0` |
| P1 | `mir_unresolved_method_const0_fails_open_2026-07-28` | **STILL-BROKEN** | record-derived | codegen-interpret-lane | `SPEC FILE VERDICT: test/01_unit/compiler/driver/bootstrap_flat_nonentry_globals_source_spec.spl outcome=ERROR declared>=1 executed=1 passed=0 failed=1 skipped=0 dropped=0` |
| P1 | `model3d_mut_engine_free_fn_six_dynamic_args_drops_mutation_2026-07-11` | **STILL-BROKEN** | declared | - | `SPEC FILE VERDICT: test/02_integration/app/model3d/model3d_nested_nodes_spec.spl outcome=ERROR declared>=8 executed=8 passed=0 failed=8 skipped=0 dropped=0` |
| P1 | `module_global_write_lost_on_frame_pop_2026-07-28` | **STILL-BROKEN** | record-derived | - | `[gc-warning] Higher-layer module 'nogc_sync_mut.db.dbfs_engine.fts.fuzzy' (family: nogc_sync_mut) imported in restricted context (family: nogc_async_mut) (higher_layer_runtime_family) [gc-warning] Hig` |
| P1 | `native_build_reports_success_for_functionless_artifact_2026-08-10` | **STILL-BROKEN** | record-derived | codegen-shellout | `SPEC FILE VERDICT: test/01_unit/compiler/driver/native_build_success_implies_functions_spec.spl outcome=ERROR declared>=2 executed=2 passed=1 failed=1 skipped=0 dropped=0` |
| P1 | `native_build_static_method_trailing_default_unresolved_2026-08-17` | **STILL-BROKEN** | record-derived | - | `    ===== end build outcome summary =====          error: native-build worker exited with code 1.  interpreter: /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple (exit code 1)FAIL —` |
| P1 | `native_concurrent_backend_spawn_not_backend_aware_join_is_2026-08-04` | **STILL-BROKEN** | record-derived | codegen-shellout | `SPEC FILE VERDICT: test/01_unit/std/perf_optimization_spec.spl outcome=ERROR declared>=51 executed=51 passed=47 failed=4 skipped=0 dropped=0` |
| P1 | `native_entry_closure_struct_return_by_value_fields_read_as_one_2026-08-17` | **STILL-BROKEN** | declared | codegen-shellout | `SPEC FILE VERDICT: test/01_unit/compiler/codegen/native_struct_return_by_value_field_read_spec.spl outcome=ERROR declared>=3 executed=3 passed=2 failed=1 skipped=0 dropped=0` |
| P1 | `native_inlined_option_return_representation_mismatch_2026-08-02` | **STILL-BROKEN** | declared | codegen-shellout | `(no output)` |
| P1 | `native_option_bool_eq_against_raw_literal_2026-08-08` | **STILL-BROKEN** | declared | codegen-shellout | `(no output)` |
| P1 | `nested_fn_in_spec_block_loses_captured_local_2026-08-04` | **STILL-BROKEN** | declared | - | `SPEC FILE VERDICT: test/01_unit/os/acpi/acpi_test.spl outcome=ERROR declared>=10 executed=10 passed=7 failed=3 skipped=0 dropped=0` |
| P1 | `paseto_v4_tampered_token_signature_accepted_2026-07-20` | **STILL-BROKEN** | declared | - | `SPEC FILE VERDICT: test/unit/lib/crypto/paseto_v4_kat_spec.spl outcome=ERROR declared>=14 executed=14 passed=8 failed=6 skipped=0 dropped=0` |
| P1 | `placeholder_lambda_as_fn_param_callback_unevaluated_2026-07-20` | **STILL-BROKEN** | declared | - | `SPEC FILE VERDICT: test/unit/lib/gc_async_immut/facade_resolution_spec.spl outcome=ERROR declared>=2 executed=2 passed=1 failed=1 skipped=0 dropped=0` |
| P1 | `prepush_hook_unpassable_native_build_oom_2026-08-17` | **STILL-BROKEN** | record-derived | - | `FAIL — control fixture (no extern) no longer builds under native-build` |
| P1 | `primitive_receiver_trait_impl_dispatch_2026-08-07` | **STILL-BROKEN** | declared | - | `SPEC FILE VERDICT: test/01_unit/language/primitive_receiver_trait_impl_dispatch_spec.spl outcome=ERROR declared>=7 executed=7 passed=6 failed=1 skipped=0 dropped=0` |
| P1 | `private_helper_name_collision_across_modules_has_2026-08-17` | **STILL-BROKEN** | declared | - | `SPEC FILE VERDICT: test/01_unit/app/build/build_targets_spec.spl outcome=ERROR declared>=34 executed=34 passed=33 failed=1 skipped=0 dropped=0` |
| P1 | `promise_new_push_reassign_same_scope_as_nested_closure_2026-07-29` | **STILL-BROKEN** | declared | - | `SPEC FILE VERDICT: test/01_unit/lib/std/concurrency/promise_spec.spl outcome=ERROR declared>=19 executed=19 passed=12 failed=7 skipped=0 dropped=0` |
| P1 | `pure_simple_cranelift_lexer_keyword_corruption_2026-07-24` | **STILL-BROKEN** | declared | - | `Build and use the pure-Simple bin/simple instead. warning: public function  file_read_text_at  has 2 co-compiled definitions with 2 differing signatures ((text,i64,i64)->Generic { name: "Result", args` |
| P1 | `pure_simple_text_extern_abi_audit_2026-07-30` | **STILL-BROKEN** | declared | codegen-interpret-lane | `SPEC FILE VERDICT: test/01_unit/compiler/backend/text_extern_abi_ptr_len_divergence_spec.spl outcome=ERROR declared>=1 executed=1 passed=0 failed=1 skipped=0 dropped=0` |
| P1 | `query_visibility_option_i64_match_exhausted_2026-07-20` | **STILL-BROKEN** | declared | - | `SPEC FILE VERDICT: test/02_integration/app/query_visibility_surfaces_spec.spl outcome=ERROR declared>=6 executed=6 passed=0 failed=6 skipped=0 dropped=0` |
| P1 | `seed_emit_object_superlinear_hang_large_module_2026-07-20` | **STILL-BROKEN** | record-derived | - | `SPEC FILE VERDICT: test/01_unit/compiler/backend/llvm_pointer_return_null_spec.spl outcome=ERROR declared>=5 executed=5 passed=0 failed=5 skipped=0 dropped=0` |
| P1 | `seed_interp_explicit_i64_default_arg_poisons_render_backgrounds_2026-07-11` | **STILL-BROKEN** | declared | - | `SPEC FILE VERDICT: test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_engine_budget_hardening_spec.spl outcome=ERROR declared>=4 executed=4 passed=3 failed=1 skipped=0 dropped=0` |
| P1 | `seed_jit_boxed_int_61bit_drops_high_bits_2026-07-22` | **STILL-BROKEN** | declared | codegen-shellout | `[jit-fallback] HIR lowering error: Unsupported feature: cannot infer field type while lowering main: struct 'RegFile64' field 'regs' [in test/01_unit/lib/hardware/rv64gc_rtl/core64_probe.spl]: whole m` |
| P1 | `seed_jit_miscompiles_soc_top_64_masked_by_fallback_2026-07-22` | **STILL-BROKEN** | declared | codegen-shellout | `[jit-fallback] HIR lowering error: Unsupported feature: cannot infer field type while lowering main: struct 'RegFile64' field 'regs' [in test/01_unit/lib/hardware/rv64gc_rtl/core64_probe.spl]: whole m` |
| P1 | `self_hosted_font_renderer_optional_field_shape_2026-07-11` | **STILL-BROKEN** | declared | stage-lane | `SPEC FILE VERDICT: test/03_system/app/simple_2d/feature/simple_2d_vector_fonts_spec.spl outcome=ERROR declared>=7 executed=7 passed=1 failed=6 skipped=0 dropped=0` |
| P1 | `selfhosted_stage4_interpreter_string_interpolation_broken_2026-07-30` | **STILL-BROKEN** | declared | stage-lane | `SPEC FILE VERDICT: test/01_unit/compiler/interpreter/string_interpolation_spec.spl outcome=ERROR declared>=3 executed=3 passed=1 failed=2 skipped=0 dropped=0` |
| P1 | `serial_usb_sigsegv_cascade_2026-05-30` | **STILL-BROKEN** | record-derived | - | `SPEC FILE VERDICT: test/01_unit/app/serial_mcp/serial_mcp_spec.spl outcome=ERROR declared>=13 executed=13 passed=11 failed=2 skipped=0 dropped=0` |
| P1 | `simple_check_parse_only_false_green_2026-07-19` | **STILL-BROKEN** | record-derived | - | `SPEC FILE VERDICT: test/02_integration/app/diagnostics/check_diagnostics_contract_spec.spl outcome=ERROR declared>=10 executed=10 passed=0 failed=10 skipped=0 dropped=0` |
| P1 | `smf_header_wire_layout_diverges_rust_vs_simple_2026-08-10` | **STILL-BROKEN** | declared | codegen-interpret-lane | `SPEC FILE VERDICT: src/compiler/70.backend/linker/test/smf_layout_parity_spec.spl outcome=ERROR declared>=7 executed=7 passed=5 failed=2 skipped=0 dropped=0` |
| P1 | `sspec_test_path_value_semantics_divergence_2026-07-20` | **STILL-BROKEN** | declared | codegen-shellout | `SPEC FILE VERDICT: test/03_system/interpreter/interpreter_system_spec.spl outcome=ERROR declared>=34 executed=34 passed=32 failed=2 skipped=0 dropped=0` |
| P1 | `stage2_native_build_link_undefined_method_symbols_2026-08-09` | **STILL-BROKEN** | record-derived | stage-lane | `Verify the implementations agree (see diff_defs pattern in this bug's investigation notes), then either fix the divergent one or add the 'symbol<TAB>file1,file2' line to scripts/check/runtime_symbol_l` |
| P1 | `stage3_current_source_hir_rss_termination_2026-08-14` | **STILL-BROKEN** | declared | stage-lane | `SPEC FILE VERDICT: test/01_unit/compiler/driver/stage3_hir_lowerer_reuse_contract_spec.spl outcome=ERROR declared>=9 executed=9 passed=2 failed=7 skipped=0 dropped=0` |
| P1 | `stage3_lookup_or_invalid_returns_unrelated_symbol_id_2026-08-18` | **STILL-BROKEN** | record-derived | stage-lane | `SPEC FILE VERDICT: test/01_unit/compiler/hir/payload_binding_contest_names_agree_source_spec.spl outcome=ERROR declared>=5 executed=5 passed=2 failed=3 skipped=0 dropped=0` |
| P1 | `stage3_native_build_segv_generic_codegen_link_path_2026-08-06` | **STILL-BROKEN** | declared | stage-lane | `SPEC FILE VERDICT: test/01_unit/compiler/mir/struct_field_order_module_qualified_spec.spl outcome=ERROR declared>=4 executed=4 passed=3 failed=1 skipped=0 dropped=0` |
| P1 | `stage3_native_build_sigsegv_call_to_zero_root_cause_2026-08-11` | **STILL-BROKEN** | declared | stage-lane | `  skip (Rust bootstrap seed): /home/yoon/dev/simple/.claude/worktrees/agent-a4f80fc0edf8c20ff/bin/simple error: no Simple compiler passed the capability probe hint: run the bootstrap, or set SIMPLE_BU` |
| P1 | `stage3_post_file_copy_exit139_2026-08-14` | **STILL-BROKEN** | declared | stage-lane | `STATUS: FAIL scalar-metadata-copy reason=compiler-missing-or-symlink ` |
| P1 | `stage3_selfhost_exit_139_2026-08-14` | **STILL-BROKEN** | declared | stage-lane | `usage: scripts/check/check-stage3-aggregate-receiver-native.shs /absolute/path/to/admitted-pure-simple-compiler ` |
| P1 | `stage3_selfhost_reaches_mir_entry_module_not_captured_2026-08-10` | **STILL-BROKEN** | declared | stage-lane | `SPEC FILE VERDICT: test/03_system/compiler/bootstrap_stage3_real_body_spec.spl outcome=ERROR declared>=1 executed=1 passed=0 failed=1 skipped=0 dropped=0` |
| P1 | `stage4_seed_interpreter_statement_dispatch_regression_2026-08-16` | **STILL-BROKEN** | declared | stage-lane | `SPEC FILE VERDICT: test/03_system/feature/js/interpreter_vars_spec.spl outcome=ERROR declared>=21 executed=21 passed=14 failed=7 skipped=0 dropped=0` |
| P1 | `starfive_check_deployed_simple_segv_2026-08-15` | **STILL-BROKEN** | declared | - | `  skip (Rust bootstrap seed): /home/yoon/dev/simple/.claude/worktrees/agent-a4f80fc0edf8c20ff/bin/simple error: no Simple compiler passed the capability probe hint: run the bootstrap, or set SIMPLE_BU` |
| P1 | `struct_field_array_pop_no_shrink_2026-07-30` | **STILL-BROKEN** | declared | codegen-interpret-lane | `SPEC FILE VERDICT: test/01_unit/lib/editor/document_service_spec.spl outcome=ERROR declared>=15 executed=15 passed=11 failed=4 skipped=0 dropped=0` |
| P1 | `test_unit_legacy_mirror_divergence_2026-08-04` | **STILL-BROKEN** | declared | codegen-shellout | `  + unit:os/vm_process_lifecycle_spec.spl   + unit:t32_mcp/file_io_facade_spec.spl check-test-tree-divergence: FAIL — 3940 diverged vs 965 baselined (3075 new, 100 fixed-but-still-baselined); 26 mir` |
| P1 | `trait_conformance_check_ignores_arity_2026-08-04` | **STILL-BROKEN** | declared | - | `  Greeter.greet on Rude: trait=2 impl=1 [same-file] test/01_unit/compiler/traits/conformance/probe_wrong_arity.spl:13  (trait test/01_unit/compiler/traits/conformance/probe_wrong_arity.spl:7)   BlockD` |
| P1 | `vmm_copyin_cross_page_bytes_lost_2026-07-20` | **STILL-BROKEN** | declared | - | `SPEC FILE VERDICT: test/01_unit/os/kernel/memory/vmm_copyin_spec.spl outcome=ERROR declared>=18 executed=18 passed=17 failed=1 skipped=0 dropped=0` |
| P1 | `web_renderer_duplicate_public_entry_binding_2026-08-04` | **STILL-BROKEN** | record-derived | - | `SPEC FILE VERDICT: test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_cpu_simd_paint_spec.spl outcome=ERROR declared>=8 executed=8 passed=6 failed=2 skipped=0 dropped=0` |
| P1 | `web_render_full_engine_call_order_nondeterminism_2026-07-12` | **STILL-BROKEN** | record-derived | - | `SPEC FILE VERDICT: test/01_unit/os/compositor/simple_web_window_renderer_spec.spl outcome=ERROR declared>=26 executed=26 passed=14 failed=12 skipped=0 dropped=0` |
| P1 | `web_render_gpu_backend_provenance_fabricated_2026-06-17` | **STILL-BROKEN** | record-derived | - | `SPEC FILE VERDICT: test/01_unit/lib/gc_async_mut/gpu/engine2d/vulkan_compute_oracle_spec.spl outcome=ERROR declared>=13 executed=13 passed=7 failed=6 skipped=0 dropped=0` |
| P1 | `web_software_oracle_blanks_text_on_budget_exhaustion_2026-08-04` | **STILL-BROKEN** | record-derived | - | `SPEC FILE VERDICT: test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_cpu_simd_paint_spec.spl outcome=ERROR declared>=8 executed=8 passed=6 failed=2 skipped=0 dropped=0` |
| P1 | `ast_env_mirror_bypasses_stale_index_guard_2026-08-01` | **TIMEOUT** | record-derived | codegen-shellout | `[use-warning] 'rt_env_cwd' is named in  use std.io_runtime.{...}  but module '/home/yoon/dev/simple/.claude/worktrees/agent-a4f80fc0edf8c20ff/src/std/io_runtime.spl' does not provide it (imported from` |
| P1 | `cranelift_unannotated_module_bool_global_tagbox_truthy_2026-07-27` | **TIMEOUT** | record-derived | - | `[enum_f64_payload_precision] (20) LLVM enum f64 payload-word ABI -> FAIL (rc got=build-failed want=30, fallback_hits=0) [tuple_return_across_call] (21) returned tuple survives another tuple call -> FA` |
| P1 | `ecc_p384_p521_sign_verify_broken_2026-07-20` | **TIMEOUT** | declared | - | `[gc-warning] Higher-layer module 'std.nogc_sync_mut.env.types' (family: nogc_sync_mut) imported in restricted context (family: nogc_async_mut) (higher_layer_runtime_family) [use-warning] 'rt_env_cwd' ` |
| P1 | `jit_i64_boundary_constant_wraps_to_negative_2026-08-09` | **TIMEOUT** | declared | codegen-shellout | `(no output)` |
| P1 | `riscv_cross_target_nil_receiver_phase3_hir_2026-07-24` | **TIMEOUT** | declared | - | `[BOOTSTRAP-PHASE] +33499ms phase2:parse:file:done build/os/generated/nvme_fw_rv32_minimal_src/logic_task_pool_cases.spl [BOOTSTRAP-PHASE] +33499ms phase2:parse:file:start build/os/generated/nvme_fw_rv` |
| P1 | `self_hosted_cli_native_build_silent_no_artifact_2026-08-14` | **TIMEOUT** | declared | stage-lane | `[gc-warning] Higher-layer module 'std.nogc_sync_mut.gpu.engine2d.sffi_rocm' (family: nogc_sync_mut) imported in restricted context (family: nogc_async_mut) (higher_layer_runtime_family) [gc-warning] H` |
| P1 | `selfhost_native_build_const_eval_mapnew_body_on_string_2026-07-17` | **TIMEOUT** | declared | stage-lane | `[trait_default] (18) trait default method dispatch (#157) -> FAIL (rc got=build-failed want=42, fallback_hits=0) [dict_struct_value] (19) struct-valued Dict m[k].field + keys() text (#189) -> FAIL (rc` |
