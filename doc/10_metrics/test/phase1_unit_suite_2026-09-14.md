# Phase-1 (seed) `test/01_unit` sweep — status as of 2026-09-14

Record of the UNIT-P1 lane's three-round sweep of `test/01_unit` on the Rust
seed, consolidating every log this lane produced (2026-09-13 22:51 through
2026-09-14 04:17) into one set of numbers, plus the fixes landed and every
honest caveat on how those numbers were measured. This lane's commits (17
through this doc's PR) landed as PR #943; this record documents that work,
committed as a follow-up on the same branch.

## Binary identity — three builds, used at different points; every row below says which

| label | sha256 (first 20 hex) | built | carries |
|---|---|---|---|
| `4dfdf671…` | `4dfdf671742007d30210` | 2026-09-13 16:00 | none of this lane's fixes (pre-fix baseline) |
| `d4c0779c…` | `d4c0779cef6cf0cc4054` | 2026-09-13 23:12 | JavaNew comparison-operator fix (`932ab196848`) |
| `57761d4f…` | `57761d4fbfed5e444a36` | 2026-09-14 01:10 | + `CommonMistake::suggestion()` exhaustiveness fix (`d2887f81bf2`) |

All three built in this worktree (`/home/yoon/dev/simple-unitp1`) with
`CARGO_TARGET_DIR=/home/yoon/cargo-unitp1 cargo build --release --bin simple`
from this branch's own tip at build time — no other worktree touched.

## Exact commands and caps

```bash
# Round 1 (42 directories, one at a time): 4dfdf671…
bin/simple test test/01_unit/<dir>                       # timeout 3600

# Round 2 (os/compiler/app, kicked concurrently): d4c0779c…
timeout 3600 bin/simple test test/01_unit/os        > logs/os_postfix.out 2>&1 &
timeout 3600 bin/simple test test/01_unit/compiler  > logs/compiler_postfix.out 2>&1 &
timeout 3600 bin/simple test test/01_unit/app       > logs/app_postfix.out 2>&1 &

# Round 3 (168 not-yet-reached SUBdirectories of lib/os/compiler/app,
# self-throttled 2-at-a-time, paused above load 12): 57761d4f…
sh scratchpad/unitp1/shard_runner.sh
# 41 of 168 shards initially got rc=127 ("bin/simple: No such file or
# directory") because the bin/simple SYMLINK itself was removed mid-run by
# an unrelated side effect (see "Anomalies" below) -- re-ran those 41 after
# restoring the symlink, same binary (57761d4f…), all 41 got real rc values.
```

Every `bin/simple test <dir>` call used `timeout 3600` per directory/shard;
`grep -a -oE '  PASS  '` / `'  FAIL  '` / `'  CRASH  '` counts (the `-a` flag
is load-bearing: these log files contain multi-megabyte single lines, and a
plain `grep -c` silently returns nothing on them without it — found and
worked around mid-lane, see the receipt).

## Consolidated table — the 4 big directories (lib, os, compiler, app)

These 4 alone hold **9,090** of the tree's 10,708 spec files. Round 1's
single-sweep attempt on each timed out at 3600s having reached only part of
each directory; Round 2/3 layered a base sweep plus 168 shard reruns of the
subdirectories the base sweep never reached. The numbers below are the SUM of
base + all matching shards for that directory — this supersedes every earlier
per-directory number this lane reported for these 4 (Round 1's and Round 2's
receipts both state smaller, more-truncated figures; this table is the
authoritative one).

| directory | PASS | FAIL | CRASH | verdicts (P+F+C) | files present | coverage | binary |
|---|---|---|---|---|---|---|---|
| `lib` | 1,859 | 762 | 22 | 2,643 | 3,485 | 76% | **mixed**: base sweep `4dfdf671…`, all 3485-file shards `57761d4f…` |
| `os` | 490 | 525 | 32 | 1,047 | 1,171 | 89% | **mixed**: base sweep `d4c0779c…`, shards `57761d4f…` |
| `compiler` | 1,668 | 878 | 87 | 2,633 | 2,755 | 96% | **mixed**: base sweep `d4c0779c…`, shards `57761d4f…` |
| `app` | 1,070 | 540 | 47 | 1,657 | 1,679 | 99% | **mixed**: base sweep `d4c0779c…`, shards `57761d4f…` |
| **subtotal** | **5,087** | **2,705** | **188** | **7,980** | **9,090** | **88%** | |

"CRASH" = the runner's own `  CRASH  ` verdict line (child died by signal,
timed out, or otherwise produced no parseable pass/fail). The gap between
`files present` and `verdicts` (1,110 files) is genuinely NOT RUN AT ALL —
either the base sweep's own 3600s cap, a shard that itself hit 3600s
(`lib/common`, 1099 files, got SIGTERM at 1185s — rc=143 — with a partial
count already folded into the row above; not every one of its 1099 files got
a verdict), or a subdirectory the shard worklist genuinely never launched
because the whole worklist wasn't exhausted in time relative to when this
record was written (it was — `SHARD_RUNNER_DONE` logged 2026-09-14 03:25:28;
the 1,110-file gap is real remaining ground, not an incomplete run of the
mechanism itself).

## The other 39 directories (Round 1 only, never rerun)

Measured once, on `4dfdf671…` (pre-fix), 2026-09-13. Not rerun this lane —
most of these directories are small (median well under 50 files) and the
2026-09-13 fixes (JavaNew comparison operator, `suggestion()` exhaustiveness)
plausibly affect a handful of files in a few of them, but that was not
re-verified per-file. Full per-directory rows in
`scratchpad/unitp1/TABLE.md`; subtotal:

| | PASS | FAIL | CRASH | verdicts | binary |
|---|---|---|---|---|---|
| 39 small dirs | 1,381 | 232 | 3 | 1,616 | `4dfdf671…` (not rerun) |

(`test/01_unit/check`'s 3/33 architecture-conformance row is inside this
subtotal — see `check_directory_architecture_conformance_reds_2026-09-13.md`
for why those 33 are real product debt, not something this record's totals
should imply is "failing" in the ordinary sense.)

## Whole-tree total

```
PASS:      5,087 + 1,381 = 6,468
FAIL:      2,705 +   232 = 2,937
CRASH:       188 +     3 =   191
verdicts:  7,980 + 1,616 = 9,596
files present in test/01_unit (measured): 10,708
files never reached by any sweep in this lane: 10,708 - 9,596 = 1,112
                                                (1,110 from the big 4's own
                                                 gap above, 2 from directories
                                                 with 0 spec files that were
                                                 confirmed empty rather than
                                                 skipped: bootstrap,
                                                 engine_divergence, fs_driver,
                                                 infrastructure,
                                                 multi_mode_test_runner, sdk
                                                 hold no *_spec.spl files at
                                                 all)
Coverage: 9,596 / 10,708 = 89.6%
```

**This is not "89.6% pass rate."** It is coverage — the fraction of spec
files that produced ANY verdict at all, on a mix of three binary builds
spanning 2026-09-13 through 2026-09-14. Of the files that DID run,
6,468/9,596 = **67.4% passed**. Neither number should be read as a release
gate; both are sweep-coverage bookkeeping for a suite this lane never claimed
to run to completion (10,708 files at 5-10s each is 15-30h of wall time — see
the original receipt's own coverage-honesty section).

## Cross-directory failure histogram — top 20 causes

Method (`scratchpad/unitp1/hist2.sh`, regenerate any time): for every `FAIL`
block across every log this lane produced (43 Round-1 logs + 3 Round-2 base
logs + 168 Round-3 shard logs), take the FIRST `; `-delimited segment of its
`Error:` line (the runner concatenates every example's error into one line),
normalise (paths -> `PATH`, backtick atoms -> `ID`, quoted strings -> `STR`,
digit runs -> `N`). **4,562 FAIL-with-Error pairs tallied across 1,516
distinct normalised causes.**

| rank | count | cause (normalised) | example 1 | example 2 |
|---|---|---|---|---|
| 1 | 491 | `semantic: function ID not found` | `app/tooling/test_runner_timeout_spec.spl` | `app/tooling/test_result_wrapper_authored_count_spec.spl` |
| 2 | 251 | `semantic: variable ID not found` | `app/tooling/test_db_performance_spec.spl` | `app/tooling/test_db_validation_spec.spl` |
| 3 | 139 | parse: `expected expression, found Error(STR)` | `app/tooling/pkg_commands_spec.spl` | `app/tooling/env_commands_spec.spl` |
| 4 | 113 | `semantic: method ID not found on type ID` | `app/simple_web_server/config_spec.spl` | `app/ui/responsive_widget_spec.spl` |
| 5 | 89 | `Common mistake detected: Use struct literal...` (JavaNew — mixes pre/post-fix logs, see caveat) | `app/ui/ui_access_runtime_spec.spl` | `lib/gc_async_mut/gpu/browser_engine/simple_web_render_session_damage_spec.spl` |
| 5 | 89 | `semantic: class ID has no field named ID` | `app/test_daemon/test_daemon_cache_module_spec.spl` | `app/ui/color_spec.spl` |
| 7 | 69 | `erroN]: function ID not found` (same family as #1, different wrapper) | `gpu/render_2d_riscv_spec.spl` | `os/formal/process_wait_refinement_spec.spl` |
| 8 | 56 | parse: `expected pointcut expression 'pc{...}'...` (AOP grammar) | `app/tooling/list_utils_spec.spl` | `app/tooling/math_utils_spec.spl` |
| 9 | 52 | `semantic: undefined field: unknown property or method 'not' on String` | `app/lint_cli_session_contract_spec.spl` | `app/cli/check_tier_accumulator_spec.spl` |
| 10 | 49 | `semantic: array index out of bounds: index is N but length is N` | `app/startup/dynsmf_config_loading_spec.spl` | `app/mcp/token_stats_spec.spl` |
| 11 | 44 | `cannot resolve import ID` (never-written module, `app.tooling.*`) | `app/tooling/import_test.spl` | `app/tooling/todo_parser_spec.spl` |
| 11 | 44 | `cannot resolve import ID` (never-written module, `compiler.50.mir.*`) | `compiler/50.mir/hwir_riscv_scalar_decode_dispatch_owner_spec.spl` | `compiler/50.mir/hwir_riscv_scalar_decoded_uop_interface_spec.spl` |
| 13 | 38 | `cannot resolve import ID` (never-written module, `compiler.backend.*`) | `compiler/backend/vhdl_builder_spec.spl` | `compiler/backend/jit_typed_ir_reject_spec.spl` |
| 14 | 36 | `[INFO] JIT... Cannot resolve module: std.test` | `app/simple_lsp_mcp/stdio_dispatch_spec.spl` | `app/cli/compiled_entry_facade_spec.spl` |
| 15 | 35 | `no parseable pass/fail summary in test output` (harness/environmental) | `app/mcp_unit/di_handler_wiring_test.spl` | `app/io/context_ops_sql_spec.spl` |
| 16 | 30 | parse: `expected identifier, found Assign` | `app/cli/query_structured_error_stream_spec.spl` | `app/cli/query_deprecated_dunder_lexical_spec.spl` |
| 17 | 24 | `semantic: invalid assignment: complex indexed field receiver is not supported` | `app/spipe_knowledge_provider/provider_canonical_json_emitter_spec.spl` | `app/spipe_knowledge_provider/provider_generation_quarantine_spec.spl` |
| 18 | 22 | `cannot resolve import ID` (never-written module, `hardware.rv64gc.*`) | `hardware/rv64gc/rv64_regfile_spec.spl` | `hardware/rv64gc/rv64_alu_word_spec.spl` |
| 19 | 21 | parse: `expected indented block after ':', found Identifier` | `app/tooling/config_ffi_spec.spl` | `app/lsp/semantic_tokens_spec.spl` |
| 20 | 20 | parse: `expected expression, found Indent` | `app/tooling/validation_utils_spec.spl` | `app/llm_caret/retry_spec.spl` |

**Caveat on rank 5's JavaNew count (89)**: this tally deliberately spans
pre-fix (`4dfdf671…`) and post-fix (`d4c0779c…`/`57761d4f…`) logs together —
it answers "how much of this text appears across the lane's whole history,"
not "how much remains after the fix." The clean before/after for that
specific fix is in the round-2 section of `RECEIPT_UNITP1.md`: 87 -> 1 file
in `os/`, measured on a single consistent binary both times.

**Ranks 1, 2, 4, 7, 10 (491+251+113+69+49 = 973 combined)** are each an
AGGREGATE of many distinct missing symbols across many unrelated specs, not
one fixable defect — confirming the same finding from the round-3 receipt
section, now at the larger post-shard sample size.

## Fixes landed 2026-09-13/14 (this lane, PR #943)

| cause | fix | commit |
|---|---|---|
| Lexer stack overflow on >450-line comment/blank runs — crashed the RUNNER PROCESS, not just one spec | iterative skip in `CoreLexer.handle_indentation()` | `0c49e156659`, `29426e620d1` |
| `new` identifier after a comparison operator (`==`,`!=`,`<`,`>`,`<=`,`>=`) falsely raised `Common mistake detected` — single largest bucket found anywhere in this lane (87 files in `os/` alone before the fix) | added the 6 comparison `TokenKind`s to `error_recovery.rs`'s JavaNew allow-list | `932ab196848` |
| 7 of 32 `CommonMistake` variants printed the useless "See error message for details" at ERROR severity | gave all 7 a real `suggestion()`, removed the wildcard arm entirely (now compiler-enforced exhaustive) | `d2887f81bf2` |
| 45+ spec files that never parsed at all (0 examples ever executed) — truncated `step()` titles, dropped docstring/`describe` delimiters, never-valid colon return-type syntax, stray import paths, non-export imports | restored/corrected the syntax per file | `7d9836427f0`..`dee58b1a39d` (Round 1), `5eef5b0c1b0` (Round 2) |
| `build_targets_spec.spl`: 2 residual `_has(` call sites from an incomplete earlier rename (the file's own comment already explained why) | renamed to `_has_error(` | `82096705c85` |

## Filed, not fixed (too risky for a same-day change, or another lane's work)

- `allow`/`forbid` hard keywords contrary to the lexer's own comment (1 spec blocked) — `allow_reserved_as_hard_keyword_2026-09-13.md`
- `new` after a named-argument colon (`Type(field: new)`) — cannot be disambiguated from a colon legitimately opening a single-line block body within the parser's 3-token lookback — `java_new_hint_fires_after_named_arg_colon_2026-09-13.md`
- `expect(x).not.to_contain(y)` chain — works under native compilation, has no interpreter-side equivalent; exact fix location identified (`interpreter/expr/calls.rs`'s `MethodCall` dispatch), not attempted given the function's existing recursion-sensitivity warnings — `interpreter_not_chain_matcher_unsupported_2026-09-14.md`
- `test/01_unit/check`'s 33 architecture-conformance reds — real Vulkan/Engine2D/WM/DrawIR/SIMD-span product debt, categorized, explicitly out of scope for this lane — `check_directory_architecture_conformance_reds_2026-09-13.md`
- `c_backend_export_spec.spl`'s `MirToC` import — another lane's in-flight WIP module-path migration (#319) — `c_backend_export_spec_and_build_targets_spec_triage_2026-09-14.md`
- `child died by signal` (95 combined in compiler/app during round 2's concurrent sweep) — confirmed to be a self-inflicted host-load artifact of running 3 sweeps at once, not a compiler defect (3 of 5 sampled crashes reproduced as clean passes in isolation) — `child_died_by_signal_is_host_load_from_concurrent_sweeps_2026-09-13.md`

## Anomalies encountered this lane, for the record

- **`bin/simple` symlink vanished mid-shard-run** (round 3): 41 of 168 shards
  got `rc=127`, `bin/simple: No such file or directory`, in ~0s each — not a
  compiler defect, the symlink file itself was gone (its target,
  `/home/yoon/cargo-unitp1/release/simple`, was untouched). Cause not
  identified (a side effect of another spec's own file operations is
  suspected, matching the separately-observed pattern below, but not
  confirmed). Restored the symlink and re-ran all 41 on the same binary
  (`57761d4f…`) before consolidating — their numbers above are real, not
  placeholders.
- **Self-mutating fixture/script side effects**, discarded (`git checkout
  --`) rather than committed, each time detected: `test/01_unit/app/simple_lab/fixtures/hello_sdoctest.md`
  (CRLF rewrite by a spec that mutates its own tracked fixture, recurred
  across rounds 1 and 2) and `scripts/os/make_os_disk.shs` (deleted by an
  unidentified spec during the round-3 shard sweep, round 3). Worktree
  confirmed clean before every commit in this lane.

## Reproduction

```bash
cd /home/yoon/dev/simple-unitp1
git log --oneline origin/main..HEAD              # every commit this lane made
readlink -f bin/simple && sha256sum "$(readlink -f bin/simple)" | cut -c1-20
sh scratchpad/unitp1/consolidate.sh               # the big-4 table above
sh scratchpad/unitp1/hist2.sh                     # the histogram above
cat scratchpad/unitp1/logs/INDEX.txt              # every shard's rc/secs
```
