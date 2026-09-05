# Bug: `bin/simple lint <file>` times out (>300s) on files above ~150-300 lines, purely as a function of line count

**ID:** lint_single_file_superlinear_timeout_on_line_count_2026-08-06
**Severity:** P1 — makes `bin/simple lint` unusable on any file over a few hundred
lines
Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 02).
(third lane, same day). NOT superlinear — **linear at ~0.19-0.20 s/line**,
replicated by two lanes on two independent synthetic families. **99.0% of the
size-dependent cost is `parse_module_silent_checked`; all of lint's own ~44
check functions together are 1.0%** (measured with zero source edits via the
`.spl` extension gate — see "Third lane" below). This is therefore a **compiler
frontend parser** performance defect that `bin/simple lint` exposes, not a
lint-tooling defect; the title's "superlinear" wording is retained only because
it is this file's ID. `module_get_decls`/decl-count are ruled OUT. No fix
landed; the remaining question is whether the constant is the parser's algorithm
or the tier it executes under.
**Reported:** 2026-08-06

---

## Correction (second lane, same day): this is NOT superlinear/quadratic — it is
## roughly LINEAR with a very large per-statement constant (~0.2-0.25s/statement)

**The original "severe superlinear (looks worse than quadratic)" framing in this
doc is not supported once measured with adequate timeouts.** Every "times out"
data point in the original table used a 40-60s timeout, which is shorter than
the file's true (linear) completion time — the earlier lane's own methodology
note says to trust timing, but a *timeout* is not a timing, it's a censored
lower bound. This lane re-ran the same synthetic-file family with generous
timeouts (up to 280s, using `Bash(timeout: 300000)` — the harness's own default
120s Bash timeout was hit once and silently truncated a `timeout 280` run at
exactly 120s with exit 143; this must be set explicitly or every long lint run
looks like a hang that isn't one) and got a clean, uncensored progression:

Using single-decl synthetic files (`fn f(a: i64) -> i64:` followed by N repeats
of `    a = a + i`, so line count = statement count + 1, isolating statement-parse
cost from decl-count effects — see "module_get_decls is NOT the driver" below):

| Statements | Lines | `bin/simple lint` wall time | Floor-subtracted (−3.3s) |
|---|---|---|---|
| 99 | 100 | 26.4s | 23.1s |
| 199 | 200 | 50.4s | 47.1s |
| 299 | 300 | 73.3s | 70.0s |
| 599 | 600 | 164.3s | 161.0s |

Pairwise fitted exponent `k` where `time ∝ N^k` (floor-subtracted):
- 99→199 (2.01x N): 2.04x time → k≈1.02
- 99→299 (3.02x N): 3.03x time → k≈1.00
- 99→599 (6.05x N): 6.97x time → k≈1.08

**This is linear (k≈1.0-1.1), not quadratic (k=2).** A true O(N²) site would
show k→2 as N grows; instead k stays flat and near 1 across a 6x range. The
per-statement cost is roughly constant at **~0.2-0.27s per statement**, which is
still a severe usability defect (a 2613-line real file at this rate is
~500-700s, matching the doc's own "originally reported 300-590s" data point
almost exactly under a *linear*, not quadratic, model) but it is a different
kind of bug: hunt an expensive-but-bounded per-statement operation (e.g. a
linear scan through a fixed-size but large table on every token/statement, a
syscall, an allocation-heavy pattern), not an accumulating-with-N algorithm.
**Whoever picks this up next should retarget the search accordingly** — the
original doc's quadratic framing and its "hunt for O(N²) in module_get_decls"
recommendation are retired by the section below.

### module_get_decls / decl count is NOT the driver — ruled out by this lane

The original doc's "next step" was to bisect `module_decl_at`'s env-var
fallback (`_Ast/module_state.spl:439-449`) as the suspected O(N²) site. This
lane ruled it out directly, with no source edits and no rebuild, by holding
total statement count fixed and varying decl count:

- 600-line file, 300 decls (150 fns × 2 lines): times out (60s budget)
- 600-line file, **1 decl** (single fn, 599 body statements): **164.3s**
  (same order, not faster) — confirmed above

Since a single-decl file is exactly as slow as a 300-decl file of the same
line count, the cost cannot be scaling with decl count. This retires
`module_get_decls()`, `module_add_decl()`, `module_decl_slots`,
`module_decl_at()`, and the whole `SIMPLE_NATIVE_ARENA_DECLS` family
(`_Ast/module_state.spl:408-449`, `_Ast/decl_nodes.spl:1294-1326`) as
candidates — do not re-bisect these.

### Other mechanisms checked and ruled out this lane (file:line, no rebuild needed)

- **`resolve_lint_config` / `apply_file_attributes`**
  (`config_and_model.spl:453-460`) returns at line 1 for any file whose first
  non-blank line starts with `fn `/`me `/`class `/etc — which is every
  synthetic repro file here. Near-zero cost on this shape. (Real files with a
  license-header/import preamble before the first `fn` may pay more here, but
  that is bounded by preamble length, not body length — not a fit for the
  observed scaling.)
- **`fmt --check`'s 21s baseline is NOT a valid comparison and should be
  retired from this doc.** `src/compiler/90.tools/formatter/main.spl` imports
  only `lexer_struct` (line 8) — it never calls `parse_module_silent_checked`
  or builds an AST at all. The original doc's "lint does strictly less than
  fmt yet is slower" argument compared two different pipelines (lexer-only vs
  full-AST) and is invalid.
- **The `expr_*`/`stmt_*` per-index env-mirror writers**
  (`_AstExpr/nodes.spl:265-314`, `ast_stmt.spl:112-207`, both called from
  `expr_alloc`/`stmt_alloc` on every node) are gated behind
  `expr_env_mirror_enabled()`/`stmt_env_mirror_enabled()`, which read
  `SIMPLE_BOOTSTRAP` once, cache the result in a module slot, and return the
  cached `false` on every subsequent call in a plain `bin/simple lint` run
  (confirmed `SIMPLE_BOOTSTRAP` unset in the test shell). Not the driver.
- **`par_kind_set`/`par_text_set`/`par_line_set`/`par_col_set`**
  (`parser.spl:122-157`, called on every `parser_advance()`, i.e. every token)
  are gated behind `par_env_save_enabled()`, also cached, also default-off.
  Not the driver.
- **`lex_snapshot_save`/`lex_snapshot_restore`** (`lexer.spl:669-694`, used for
  speculative/backtracking lookahead e.g. `try_parse_bare_ident_string_call`,
  the `loop:`-statement lookahead) save/restore a fixed ~10-field struct plus a
  bounded indent-stack — not position- or history-dependent. Not the driver.
- **`.push()` on `[i64]`/`[text]` module-var arrays** — **inconclusive, not
  ruled out.** A standalone probe (`push_bench.spl`, 30,000 `.push()` calls
  across 4 sizes) compiled via `bin/simple compile` to SMF and executed via
  `bin/simple <file>.smf` completed in 29ms total, suggesting amortized O(1)
  push in whatever backend executes SMF. But `bin/simple compile`/`run` route
  through a different execution path than the natively-compiled `lint`
  command inside the deployed binary (both print the same
  "Rust-built Simple binary is a bootstrap seed only" banner as `lint` does —
  see below — so this is a shared-shim artifact, not proof of which backend
  actually ran the push loop). **This probe does not conclusively test the
  code path lint uses.** Do not cite it as ruling out `.push()`.
- **The "Rust-built Simple binary is a bootstrap seed only" warning banner
  printed by `bin/simple lint`/`fmt`/`compile`/`run` alike is a dead end, not
  evidence of seed delegation.** Source: `driver/src/main.rs:104-105`,
  unconditional unless `SIMPLE_RUST_SEED_WARNING=0` / `SIMPLE_BOOTSTRAP=1` /
  `--seed-ok` (`driver/src/seed_warning.rs`). Confirmed
  `bin/release/x86_64-unknown-linux-gnu/simple` (58,865,936 bytes) is NOT the
  seed binary (`src/compiler_rust/target/bootstrap/simple`, 33,258,368 bytes,
  different md5) — it is the deployed self-hosted binary, which apparently
  links the same Rust host-shim crate for its process entry point. This banner
  firing is consistent with normal self-hosted operation and should not be
  chased as a delegation bug by the next lane, though it may be worth a
  separate cosmetic bug report (the warning text is misleading on a
  self-hosted binary).

### Precise next step for whoever continues this

The remaining candidate is unglamorous but narrow: some operation inside
`parse_statement()` → `parse_expr()` → `expr_alloc()`/`stmt_alloc()`
(`parser_stmts.spl`, `parser_expr.spl`, `_AstExpr/nodes.spl:476-499`,
`ast_stmt.spl:252+`) costs on the order of 0.2-0.25s **per statement**,
independent of N (i.e. NOT accumulating with N — the exponent is ~1, not
growing). That constant is enormous for parsing `a = a + <int>` — candidates
worth instrumenting first: `keyword_lookup()` (called per identifier-like
token in several `parse_statement` branches — check if it's a linear scan
over a large keyword table rather than a hash lookup), span/position
bookkeeping, or any syscall/allocation happening once per statement.

**Concrete bisection recipe (requires ONE T3 full bootstrap — budget 15-45min,
has been observed to die mid-stage3 in this repo today, see
`build/bootstrap/bootstrap-progress.log`; do not attempt more than one
iteration per session without checking that budget):**

1. Edit `parse_block()` (`parser_stmts.spl:246-274`) so the indented-block
   branch's `while true:` loop still consumes tokens to the matching dedent
   (kind 182) but does NOT call `parse_statement()`/`stmts.push(s)` — return
   `[]` instead. This must still consume the right tokens (skip to dedent) so
   the rest of the file continues to parse; do not just `return []`
   unconditionally without draining tokens, or every subsequent top-level decl
   will desync.
2. Rebuild + deploy: `scripts/bootstrap/bootstrap-from-scratch.sh --deploy`.
3. Time `syn_1decl_599stmt.spl` (600 lines, 1 decl, in
   `/tmp/.../scratchpad/lintperf/` this session, or regenerate: a `fn` header
   followed by 599 `a = a + i` lines).
4. If it flips to fast (sub-5s): the cost is inside per-statement parsing
   itself (statement/expr construction) — instrument `parse_statement`'s
   default expression-statement branch and `expr_alloc` next.
5. If it is still ~164s: the cost is in something reached even when
   statements aren't built — check `parser_skip_newlines_and_semicolons()`
   (called once per loop iteration regardless) and the lexer's per-token path
   itself (contradicting the `fmt`-uses-lexer-only observation above, which
   would then need re-examination for what state lint's lexer usage differs
   on).

**When re-measuring timeouts: always pass the Bash tool's own `timeout`
parameter generously (e.g. 300000ms) in addition to any inner shell
`timeout N`.** This lane lost one data point to the harness's 120s default
Bash timeout silently truncating a `timeout 280` command at 120s (exit 143,
"Command timed out after 2m 0s") — indistinguishable from a real hang unless
you notice the exit code and elapsed time don't match your inner `timeout`
value.

---

## Third lane (2026-08-06, later same day): linearity replicated on a second
## synthetic family, and the parse-vs-checks split MEASURED — parse is 99%

This lane reproduced from scratch and independently reached the same linear
verdict as the second lane, on a *different* synthetic shape — so the linear
finding is now a two-family, two-lane replication rather than one lane's fit. It
also closes the question the second lane's section ends on ("is the ~0.2s/statement
constant inside `parse_module_silent_checked` or somewhere in the lint checks?")
**with a number, without a bootstrap, and without a single source edit**, using
an entry-point gate that was already in the code.

**Binary under test:** `bin/simple` → `bin/release/x86_64-unknown-linux-gnu/simple`
(58,865,936 bytes, mtime 2026-08-06 21:47) — the same binary the second lane
measured. Every timing below is wall-clock from that binary with the
`/proc/loadavg` 1-minute load recorded per sample. This box had two concurrent
stage-3 compiles and ~10 other agent sessions running throughout, so **only
back-to-back relative comparisons are load-safe**; contended samples are flagged.
Reproducibility check: `syn_100.spl` measured 42.84s / 41.68s / 41.85s in three
separate runs at loads 9.41 / 7.91 / 10.35 — under 3% spread across a 30% load
swing, so these numbers are not load-noise artifacts.

### Curve on a second synthetic family (N decls, not 1 decl) — also linear

The second lane's family was 1 decl + N body statements. This lane used the
opposite shape: N two-line declarations
(`fn synthetic_fn_<i>(a: i64) -> i64:` / `    a + <i>`). If the constant were
decl-driven, the two families would disagree. They do not.

| File | Decls | Lines | lint wall | −floor (3.43s) | s/line | load |
|---|---|---|---|---|---|---|
| `tiny.spl` | 1 | 2 | 3.42s | — (floor) | — | 7.61 |
| `syn_10.spl` | 10 | 20 | 7.85s | 4.4s | 0.22 | 6.77 |
| `syn_25.spl` | 25 | 50 | 12.98s | 9.6s | 0.19 | 6.8 |
| `syn_50.spl` | 50 | 100 | 25.60s | 22.2s | 0.22 | 7.0 |
| `syn_100.spl` | 100 | 200 | 42.84s | 39.4s | 0.197 | 9.41 |
| `syn_200.spl` | 200 | 400 | 83.78s | 80.4s | 0.201 | 7.30 |
| `syn_400.spl` | 400 | 800 | 154.65s | 151.2s | 0.189 | 6.91 |

Fitted exponent, floor-subtracted: 200→400 lines is 2.04x time for 2x input
(k≈1.03); 400→800 lines is 1.88x time for 2x input (k≈0.91). **k≈0.9-1.0 across
a 4x range on the N-decl family, matching the second lane's k≈1.0-1.1 on the
1-decl family.** Two shapes, two lanes, same answer: linear, ~0.19-0.20 s/line,
no accumulating term. Extrapolating 0.195 s/line to the reported real file
(`simple_web_html_layout_renderer_layout.spl`, 2613 lines) gives ~513s — inside
the originally reported 300-590s band **with no superlinear term required**.
The H1 of this doc is retained only because it is the file's ID; the title's
"superlinear" wording is wrong and the Status line above is authoritative.

`bin/simple fmt --check` on the identical files: 3.52s / 10.50s / 16.89s /
29.39s for 2 / 200 / 400 / 800 lines — also linear, ~0.033 s/line. Recorded as a
scale reference only: per the second lane, fmt is lexer-only and does **not**
bound lint's parse cost, so no attribution is drawn from it.

### Parse vs. lint-checks: split measured via the existing `.spl` extension gate

`lint_cli_source` (`src/compiler/90.tools/lint/_LintMain/entry_and_fixes.spl:35-38`)
runs `linter.lint_source(path, content)` **unconditionally first**, and only then
does `if not path.ends_with(".spl"): return results`. So linting the same bytes
under a `.txt` name runs the entire `Linter.lint_source` body — the per-line
`check_line` loop, all 17 whole-content `self.check_*` calls, and
`check_all_rules` — while skipping `parse_module_silent_checked` and the 6
AST-based decl checks. Linting one file under two extensions therefore splits the
constant exactly, with zero source edits and no rebuild. **This replaces the
T3-bootstrap bisection recipe the second lane proposed; it costs 8 seconds.**

| Same bytes, two extensions | Lines | wall | above 3.43s floor | load |
|---|---|---|---|---|
| `tiny.txt` | 2 | 3.43s | — (floor) | 6.15 |
| `syn_100.txt` — checks only | 200 | **3.72s** | **0.29s** | 6.13 |
| `syn_100.spl` — checks + parse | 200 | 42.84s | 39.41s | 9.41 |
| `syn_400.txt` — checks only | 800 | **4.64s** | **1.21s** | 6.12 |
| `syn_400.spl` — checks + parse | 800 | 154.65s | 151.22s | 6.91 |

**Verdict: 99.0% of the size-dependent cost is `parse_module_silent_checked` +
the AST decl checks; every lint check lint actually owns costs 1.0%.** At 800
lines that is 150.0s of parse against 1.2s of checks (0.0015 s/line — negligible
and itself linear). The same 99/1 split holds at 200 lines, so it is not a
crossover effect.

Consequences:

- The **first** lane's stubbing result ("stubbed all ~44 check functions, still
  times out") was *correct*, not a stale-binary artifact — it is now corroborated
  by an independent method that touches no source. That lane's conclusion was
  sound and the doubt cast on it by its own eprint-ordering caveat can be lifted.
- Combined with the first lane's stubbing of the 6 decl checks in
  `entry_and_fixes.spl` (`check_argument_count`, `check_collection_patterns`,
  `check_stub_impl`, `check_star_export_file`, `check_wide_public_file`,
  `check_option_me_call_source`) leaving it slow, the 99% narrows further to
  **`parse_module_silent_checked` itself**, i.e. the parser, not lint.
- **Do not spend any more effort on the lint check functions, `check_all_rules`,
  the ~30 `content.split("\n")` sites, or `resolve_lint_config`.** Their combined
  contribution is ~1%. This is a compiler-frontend parser performance defect that
  `bin/simple lint` merely exposes, not a lint-tooling defect.
- **Also ruled out by the same number: findings-count / `.push()` cost.** See
  below — but note it would have to live in the 1% anyway.

Secondary datapoint: `syn_400.spl` copied under a path containing `src/lib/`
(which un-gates `check_param_tag_spl`, `lint_checks.spl:320-323`) took 165.4s at
load 12.94 vs 154.6s at load 6.91 — i.e. within the load difference and
consistent with the 1% budget. Path-gated checks are not a hidden term for the
reported `src/lib/**` files.

### The lint tool is parsed from `.spl` on every invocation (explains the floor)

`strace -f -e trace=openat bin/simple lint tiny.spl` on a **2-line** target
records **554 `.spl` file opens**, including `src/app/cli/lint_entry.spl`, the
whole `src/compiler/90.tools/lint/_LintMain/` and
`src/compiler/90.tools/fix/rules/impl_/` trees, and
`src/lib/nogc_sync_mut/tooling/easy_fix/*`. Independently, `bin/simple lint
--help` emits parser deprecation warnings sourced from
`src/lib/nogc_async_mut/env/paths.spl:5-6` — it is parsing the linter's own
dependency tree before it can print usage.

This is the mechanical explanation for the **~3.43s fixed floor** every lint
invocation pays regardless of target size. It also reframes the second lane's
closing puzzle ("0.2s per statement is enormous for parsing `a = a + i`"): if
the pure-Simple parser is itself executing under the host engine rather than as
compiled native code, a ~0.19 s/statement constant needs no exotic per-statement
culprit (a linear `keyword_lookup` table scan, per-statement syscall, etc.).
**This is a hypothesis, not a conclusion** — but it is far cheaper to check than
instrumenting `parse_statement` behind a T3 bootstrap, so check it first. It does
not contradict the second lane's binary-identity finding: a deployed self-hosted
binary can still load its tool front-ends from source.

### Ruled out this lane

- **Seed `.push()` clone cost is NOT a meaningful term.** `.claude/rules` records
  that the seed's `.push()` always clones, which would make `self.results.push()`
  quadratic in *finding count* — a term invisible on clean synthetic files and a
  plausible real superlinear mechanism on real sources. Tested by holding size
  fixed and varying finding count (PascalCase `fn SyntheticFnN` names trip ST001,
  which is pushed into `self.results` before the config filter suppresses it),
  A/B/A/B interleaved and serial:

  | | clean | +100/200 findings | delta |
  |---|---|---|---|
  | 200 lines, rep 1 | 41.68s | 43.29s | +3.9% |
  | 200 lines, rep 2 | 41.85s | 46.73s | +11.7% (load 10.3) |
  | 400 lines, rep 1 | 76.41s | 77.48s | +1.4% |
  | 400 lines, rep 2 | 84.25s | 79.59s | **−5.5%** |

  The delta does not grow with N and changes sign between reps — it is load
  noise, not an O(findings²) term. Ruled out.
- **earlyoom is NOT killing these runs.** `journalctl --since "12 hours ago"`
  shows only earlyoom's hourly heartbeat lines and **zero kill lines**; available
  memory never dropped below 40% of 128 GiB, and a running `bin/simple lint`
  peaks around 350 MB RSS. Combined with the second lane's finding that the
  harness's own 120s default Bash timeout truncates at exit 143, **today's
  exit-143 "lint killed with no verdict" reports across several lanes were
  harness timeouts on a genuinely slow but linear lint, not OOM kills.** That
  wrong explanation was circulating between lanes and should be retired.
- **Path-gated whole-content checks are already cheap.** `check_theme_package`
  (`lint_checks.spl:302-304`), `check_stale_md_diagrams` (`:731-733`) and
  `check_param_tag_spl` (`:320-323`) all early-return on a path test before
  touching `content`, so "gated checks scanning content they discard" is not an
  available easy win — and per the 99/1 split it could not have been.

### Why no code fix shipped from this lane

The 99% sits in `parse_module_silent_checked` — the compiler frontend parser, not
`src/compiler/90.tools/lint/`. There is no minimal lint-layer diff that moves it,
and a lint-side workaround would be exactly the kind of cover-up this repo's
rules forbid. Per the standing rule that a runtime/frontend root cause is filed
precisely rather than papered over at the tool layer, this lane's deliverable is
the measurement above. **No source file was modified by this lane**, so there is
no sabotage check to report — sabotage evidence is only meaningful for a shipped
diff.

### Precise next step (revised)

Ignore the whole lint call graph. Reproduce the ~0.19 s/line on the parser alone,
then determine whether the cost is the parser's algorithm or the tier it executes
under — the second question is cheap (compare a `parse`-only invocation against
the same parse inside a natively-compiled artifact) and, if the tier explains it,
the per-statement hunt (`keyword_lookup`, span bookkeeping, per-statement
syscalls) the second lane proposed is unnecessary.

---

## Summary

Two independent lanes this session hit `bin/simple lint <file>` never completing
(300-590s+) on:

- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl`
  (2613 lines, 142,853 bytes, 73 top-level `fn`/`me` signatures, only 2 `use`
  imports)
- `src/lib/gc_async_mut/gpu/browser_engine/containment.spl`

A standing project note ("`bin/simple lint` scans the whole repo tree regardless
of the file argument") was floated as the explanation. **That theory is false**
— see "Ruled out" below. The real mechanism is a severe superlinear (looks
worse than quadratic) blow-up in wall-clock time as a function of the target
file's own line/declaration count, reproducible on **purely synthetic,
content-free** input. This is NOT the same defect as
`doc/08_tracking/bug/ast_env_var_quadratic_parse_2026-06-13.md`, even though it
has the same shape and that doc's proposed fix was tried and does not help —
see "Distinct from the known env-var quadratic bug" below.

---

## Ruled out: "lint scans the whole repo tree"

Read, not guessed:

- `src/app/io/cli_lint_commands.spl:143-165` (`run_lint_command`) — a non-directory
  target is pushed into `lint_files` as exactly one entry; `discover_spl_files`
  (repo/dir walk) is only called when the target `is_dir(target)`. A file
  target never triggers directory discovery.
- `src/compiler/90.tools/lint/_LintMain/entry_and_fixes.spl:35-38`
  (`lint_cli_source`) parses only the given file's own `content` string via
  `parse_module_silent_checked(content, path)` — no transitive import
  resolution.
- The slow target file has exactly 2 `use` imports, both within the same
  directory (`layout_table`, `containment`).

**Verdict: scoping is correct.** A single-file target lints exactly that file.
The "whole repo" folklore should be retired.

---

## Empirical timing (synthetic reproducer, content-independent)

Generator (write with `Write`, not `python3` — the ad hoc python was scratch-only,
never committed, kept here as prose since repo rules forbid Python in
committed artifacts):

> For `n` in {50, 150, 300, 1300}: write `n` repetitions of
> ```
> fn synthetic_fn_<i>(a: i64) -> i64:
>     a + <i>
> ```
> to a `.spl` file (no imports, no classes, no strings — content-minimal).

| File | Lines | Bytes | `bin/simple lint` result |
|---|---|---|---|
| 3-line trivial (`fn main(): print "hi"`) | 3 | ~30 | 3.3s, completes |
| `syn_50.spl` (50 fns) | 100 | ~2.5K | **20.1s**, completes |
| `syn_150.spl` (150 fns) | 300 | ~7.5K | times out, >40s |
| `syn_300.spl` (300 fns) | 600 | ~15K | times out, >60s |
| `syn_1300` (1300 fns) | 2600 | 62,780 | times out, >60s |
| real target file (73 fns, real content) | 2613 | 142,853 | times out, >100s (originally reported 300-590s) |
| real target file, half (1300 lines) | 1300 | 69,532 | times out, >90s |
| real target file, two giant 7062-char lines truncated to one-liners | 2613 | smaller | still times out, >60s (giant lines are NOT the driver) |

Reference for comparison: `bin/simple fmt --check` on the **same** `syn_300.spl`
(600 lines) — which also fully parses the file — completes in **21.0s**. Slow,
but not a hang. `lint` on the identical file, with every one of its own lint
*checks* stubbed out (see below), still does not finish in 60s. The
lint-specific delta over `fmt --check` is real and is not explained by parsing
alone.

The 100→20s single data point against fmt's 600→21s is not enough to fit an
exact exponent, but the shape (a 3-line file in 3.3s, a 100-line file in 20s, a
300-line file not finishing in 60s) is consistent with the superlinear/quadratic
family already seen elsewhere in this codebase (`.claude/memory` "Measurement
traps" and "Compiler/language defects" quadratic entries) and matches the
*shape* — though not, per the section below, the *site* — of the tracked
`ast_env_var_quadratic_parse_2026-06-13` bug.

---

## Localization performed (behavioral bisection, not print-probes)

**Important methodological note for whoever picks this up:** `eprint` inside
this call graph is **not reliable ordering evidence**. In one run, `before
check_all_rules call` and `after check_all_rules` both printed while the eprint
that is the literal first statement inside `check_all_rules` never printed —
impossible under honest ordered output. Every earlier working hypothesis this
session built purely on "probe X never printed" (interpreter fallback at the
`check_all_rules` call boundary, hang inside
`_collect_duplicate_typed_arg_signatures`) was retracted for exactly this
reason. **Only wall-clock timing on a stubbed-out call graph is trustworthy
here** — verified by editing the actual `.spl` source (not env vars, not
flags) to `return []`/skip a call, then timing.

Behavioral bisection performed on `syn_300.spl` (600 lines), each stub reverted
immediately after measurement (`git diff --stat` confirmed byte-identical to
`main` after every revert — see "Housekeeping"):

1. **`check_all_rules()` (the 24-rule EasyFix registry, `registry.spl`) stubbed
   to return `[]` entirely** — still times out at 60s. Not the driver.
2. **`Linter.lint_source`'s per-line `check_line` loop AND all 17 whole-content
   `self.check_*` calls stubbed out**, `check_all_rules` also still stubbed —
   still times out at 60s. Not the driver.
3. **All 6 decl-based checks in `entry_and_fixes.spl`
   (`check_argument_count`, `check_collection_patterns`, `check_stub_impl`,
   `check_star_export_file`, `check_wide_public_file`,
   `check_option_me_call_source`) also stubbed to empty**, on top of 1 and 2 —
   **still times out at 60s.**

At this point every lint *check* function reachable from `run_lint_file` is a
no-op; the only work left in the call graph is:
`parse_module_silent_checked(content, path)` (the parse gate) →
`resolve_lint_config` → `module_get_decls()` → `content.split("\n")`.

`fmt --check` on the identical file (which also fully parses) completes in
21s. The stubbed-lint path, doing strictly less work than `fmt --check` plus
one call to `module_get_decls()`, still does not finish in 60s. This points at
either the parse step behaving differently under the lint entry point than
under the fmt entry point, or `module_get_decls()` / its `module_decl_at()`
backing store.

**Not fully pinned within this session's effort budget.** The next step is to
stub `module_get_decls()` itself (return `[]` without calling
`ast_module_decl_count_get()`/`module_decl_at()`) and re-time; if that flips it
to fast, the culprit is confirmed as `module_decl_at()`'s environ-scan fallback
in `src/compiler/10.frontend/core/_Ast/module_state.spl:439-449`; if not, the
parse gate itself (`parse_module_silent_checked`) needs the same bisection
treatment, or the divergence from `fmt --check`'s 21s needs to be explained
directly (they should call largely the same parser).

---

## Distinct from the known env-var quadratic bug — tried and does NOT fix this

`doc/08_tracking/bug/ast_env_var_quadratic_parse_2026-06-13.md` documents a real,
already-localized O(N²) defect: AST node reads/writes falling back to
`rt_env_get`/`rt_env_set` (linear `environ[]` scan) instead of the arena
arrays, gated by `SIMPLE_NATIVE_ARENA_DECLS`. Given the matching shape (52s/146s/
timeout at N=100/200/400 in that doc vs. this session's 20s/timeout/timeout at
n=50/150/300), this looked like the same bug. It is not, or at least setting the
documented flag does not reproduce that doc's claimed fix here:

- `src/compiler/10.frontend/core/_Ast/decl_nodes.spl:141-166` — a 2026-07-24
  follow-up already made **arena-preferred the default** for per-decl-field
  reads/writes (`ast_decl_arena_default()` returns 1 unless
  `SIMPLE_BOOTSTRAP==1`, which ordinary `bin/simple lint` never sets). So the
  specific mechanism the 2026-06-13 doc fixes for is **already off by default**
  in a plain lint run — no flag needed.
- `src/compiler/10.frontend/core/_Ast/module_state.spl:439-449`
  (`module_decl_at`) is a **separate, inconsistent** accessor that was not
  updated to match: it hardcodes `rt_env_get_i64("SIMPLE_NATIVE_ARENA_DECLS", 0)`
  — default **0** (slow path), not `ast_decl_arena_default()`'s default of 1.
  This looked like a promising, narrow, bounded fix target.
- **Tried and falsified, twice:**
  1. In-process fix: `src/app/io/cli_lint_commands.spl`'s `run_lint_command`
     wrapped the file-processing loop in
     `env_set("SIMPLE_NATIVE_ARENA_DECLS", "1")` / restore-after, mirroring the
     exact precedent already in `src/app/io/_CliCompile/compile_targets.spl:1114`
     (which does this around native-build compiles). **No effect** — `syn_300.spl`
     still timed out at 60s with the flag set from inside the running process.
  2. Exogenous fix, to rule out an in-process JIT-caching/staleness explanation:
     `SIMPLE_NATIVE_ARENA_DECLS=1 bin/simple lint syn_300.spl` (flag set in the
     real OS process environment from the shell, before the process even
     starts). **Also no effect** — still timed out at 40s (tested with a
     shorter budget).

Both attempts were reverted; `git diff --stat` against `main` is empty for
every file touched this session (see Housekeeping). **The
`SIMPLE_NATIVE_ARENA_DECLS` flag is not the lever for this specific hang.**
Either `module_decl_at` isn't actually the bottleneck (consistent with the
bisection above, which never got to isolate it cleanly since stubbing its only
caller, `module_get_decls`'s 6 consumers, didn't help either — the parse gate
itself was never separately stubbed), or there is a second, distinct
quadratic site this session did not reach.

---

## What a future session should do

1. **Trust timing, not `eprint` ordering**, in this call graph — see the
   methodological note above.
2. Bisect `parse_module_silent_checked` vs `module_get_decls()` directly (stub
   each to a constant, one at a time, and re-time `syn_300.spl`) to finish the
   localization this session left at "somewhere in the parse+decl-collection
   prefix, not in any of the ~44 individual lint check functions."
3. If it lands back in `_Ast`/`module_state.spl`, treat as a sibling of
   `ast_env_var_quadratic_parse_2026-06-13` (same file family, same author
   intent) rather than reopening that doc — the earlier fix already shipped
   for the sibling accessor family; this is either a second un-migrated
   accessor or a genuinely different mechanism.
4. Confirm on the real target file
   (`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl`)
   once a fix candidate exists — the synthetic reproducer is enough to
   iterate cheaply, but the real file (73 fns, 2613 lines, 142KB) is the actual
   user-facing case and should complete well under 120s post-fix with byte-
   identical lint findings to a (very patient) pre-fix run.

---

## Housekeeping

All instrumentation (eprint probes) and both attempted fixes were reverted.
Verified with `git diff --stat` against `main` for every file touched this
session — empty in every case:
`src/compiler/90.tools/lint/_LintMain/entry_and_fixes.spl`,
`src/compiler/90.tools/lint/_LintMain/lint_checks.spl`,
`src/compiler/90.tools/fix/rules/registry.spl`,
`src/compiler/90.tools/fix/rules/impl_/lint_spec.spl`,
`src/compiler/90.tools/fix/rules/impl_/lint_code.spl`,
`src/app/io/cli_lint_commands.spl`. No code change shipped from this
investigation; this doc is the only artifact.

---

## Re-verification 2026-08-17 (compiler-lint lane) — OPEN, evidence-only, NO perf fix attempted

Per explicit task scope this row is a **known cost property**; no performance
change was attempted and none should be attempted opportunistically.

State of the evidence in current source:

- `src/compiler/90.tools/lint/main.spl` is unchanged with respect to this record
  — the investigation on 2026-08-06 shipped no code (see the Housekeeping
  section above, which verifies `git diff --stat` empty for all six files it
  touched). Nothing has superseded it since.
- The cost model has since been **re-measured independently** and is now pinned
  in `.claude/rules/commands.md` (2026-08-17 table). That measurement corrects
  the older "~3.3-4.0s per function decl" figure in two ways that matter here:
  declaration count alone scales **linearly** (15 -> 90 decls leaves per-decl
  cost flat or falling), while **content complexity** is the superlinear driver
  — `zca_rows.spl` first 2 fns cost ~99s/decl and first 8 fns exceeded 2400s.
  So "superlinear on line count" is close but not exact; it is superlinear on
  per-declaration content, which correlates with line count within one file.
- It is a **cost** problem, not a hang: the linter does terminate and does print
  a verdict. Confirmed again this session — an unrelated single-file lint of
  `src/lib/nogc_sync_mut/spec/decorators.spl` (331 lines, 10 decls) produced
  real diagnostics rather than hanging.
- The cost is now gated: `sh scripts/check/check-lint-cost-budget.shs`
  (fail-closed, `--selftest`, treats a silent exit 0 with no verdict line as
  FAIL).

**Verdict: OPEN (accepted cost property, gated).** The superlinear term has
still not been localised; attach-based profiling remains blocked on this host
(`ptrace_scope=1`, `perf_event_paranoid=4`). Cross-reference:
`doc/08_tracking/bug/lint_timeout_hwir_zca_rows_2026-08-17.md`.
Not proven here: any specific hot function or algorithmic cause.
