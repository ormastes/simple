# U1.3 patch prep: coverage-primitive prerequisites — exact diffs, verification, ordering

- **Date:** 2026-08-07
- **Type:** Patch-preparation doc, NOT a landed change. No Rust code has been
  edited by this doc; all diffs below are proposed, unapplied, for a later
  isolated bootstrap session to apply and build.
- **Why doc-only:** repo disk at 94% (239G free), `src/compiler_rust/target`
  alone 126G, and this repo has been ENOSPC-wiped to near-zero files twice.
  Five concurrent agent sessions were writing at the time this doc was
  prepared. A Rust seed build here risks a catastrophic tree wipe.
- **Source docs:** `doc/03_plan/ui/testing/wm_gui_web_system_test_coverage_plan_2026-08-07.md`
  (U1.3 entry), `doc/08_tracking/bug/coverage_tooling_does_not_instrument_spl_2026-08-07.md`,
  `scripts/check/check-render2d-coverage.shs`.

## How to read this doc

Each prerequisite section states: the file:line (re-verified against the
current working tree, not trusted from the bug doc without a re-read), the
exact anchor text at that location, the proposed diff, the verification step
mapped onto the gate script's rows, and any correction to the bug doc's
original claim. A "risks and unknowns" section follows with everything that
could not be confirmed statically.

**Important correction up front:** the bug doc's file path for prerequisite 1,
`src/compiler_rust/compiler/src/interpreter_call/core/interpreter_control.rs`,
**does not exist**. The real file is
`src/compiler_rust/compiler/src/interpreter_control.rs` (no
`interpreter_call/core/` subdirectory in this tree). Line numbers below are
re-verified against that real file, not copied from the bug doc.

---

## Prerequisite 3: `bin/simple spl-coverage` dispatchable (highest confidence — do this first)

### Root cause, precisely located

`src/compiler_rust/driver/src/main.rs` has a declarative `COMMAND_TABLE: &[CommandEntry]`
(lines 407-997) that `dispatch_command` (line 147) searches by name
(`COMMAND_TABLE.iter().find(|e| e.name == cmd)` at line 1179). There is **no
entry named `"spl-coverage"`** in the table, even though
`src/app/spl_coverage/main.spl` exists (152 lines, a working CLI with
`dump`/`status`/`clear` subcommands backed by `app.io.mod.{coverage_dump_sdn,
coverage_enabled, coverage_clear}`). When the first arg doesn't match any
`CommandEntry.name`, dispatch falls through to `handle_file_execution` (line
1638), which treats the arg as a file path, fails to resolve it, and prints
the observed `error: file not found: spl-coverage` at
`src/compiler_rust/driver/src/main.rs:1674`.

A sibling entry named `"coverage"` (pointing at the *different* file
`src/app/coverage/main.spl`) already exists at lines 924-933 and is the exact
template to copy — an "app-only" entry whose Rust fallback just errors:

```rust
    // Coverage (app-only)
    CommandEntry {
        name: "coverage",
        app_path: "src/app/coverage/main.spl",
        rust_handler: Handler::Custom(|_| {
            eprintln!("error: coverage app not found (install Simple or run from project root)");
            1
        }),
        env_override: "",
        needs_rust_flags: &[],
    },
    // Dependency graph (app-only)
```

### Proposed diff 1 — add the `spl-coverage` command entry

File: `src/compiler_rust/driver/src/main.rs`, insert immediately after the
`"coverage"` entry's closing `},` (currently line 933, before the
`// Dependency graph (app-only)` comment):

```diff
     // Coverage (app-only)
     CommandEntry {
         name: "coverage",
         app_path: "src/app/coverage/main.spl",
         rust_handler: Handler::Custom(|_| {
             eprintln!("error: coverage app not found (install Simple or run from project root)");
             1
         }),
         env_override: "",
         needs_rust_flags: &[],
     },
+    // Simple-source branch/decision coverage CLI (app-only)
+    CommandEntry {
+        name: "spl-coverage",
+        app_path: "src/app/spl_coverage/main.spl",
+        rust_handler: Handler::Custom(|_| {
+            eprintln!("error: spl-coverage app not found (install Simple or run from project root)");
+            1
+        }),
+        env_override: "",
+        needs_rust_flags: &[],
+    },
     // Dependency graph (app-only)
```

### Proposed diff 2 — mark it a pure-Simple tool (consistency with sibling `"coverage"`)

File: `src/compiler_rust/driver/src/main.rs`, function
`command_is_pure_simple_tool` (starts ~line 265). `"coverage"` is already in
this match list; add `"spl-coverage"` next to it so a missing `.spl` app
fails closed (`error: pure-Simple tool 'spl-coverage' unavailable; refusing
Rust fallback`) instead of silently trying a nonexistent Rust handler:

```diff
             | "todo-scan"
             | "todo-gen"
             | "brief"
             | "dashboard"
             | "coverage"
+            | "spl-coverage"
             | "depgraph"
```

(Exact surrounding lines must be re-read at apply time — this function's
member order may drift; anchor on the literal `| "coverage"` line, which was
re-verified present in the current tree.)

### Proposed diff 3 — REQUIRED, not optional: `dispatch_to_simple_app` has its own separate allowlist

Diffs 1 and 2 alone are **not sufficient**. `dispatch_command`'s step 3 calls
`dispatch_to_simple_app(entry.app_path, ...)` (main.rs:1254), and that
function opens with its own large allowlist of `app_relative_path` string
literals — anything not in the list hits `return None;` immediately (the
`if app_relative_path != "..." && app_relative_path != "..." ... { return
None; }` block, lines 1257-1300). `src/app/spl_coverage/main.spl` is
**not** in that list today. Without adding it, `dispatch_to_simple_app`
returns `None` for the new entry, dispatch falls through to the
`pure_simple_tool` check (diff 2 above put `"spl-coverage"` in that list),
which then prints `error: pure-Simple tool 'spl-coverage' unavailable;
refusing Rust fallback` and returns 1 — a **different** failure than today's
`file not found`, but still not dispatching to the app.

Two separate additions are required, both by exact-string match against the
sibling entry for `"spec-coverage"` (`src/app/spec_coverage/main.spl`), which
already has both:

```diff
         && app_relative_path != "src/app/spec_coverage/main.spl"
+        && app_relative_path != "src/app/spl_coverage/main.spl"
         && app_relative_path != "src/app/replay/main.spl"
```

(in the big `if ... != ... { return None; }` allowlist, main.rs ~line 1281)

```diff
             | "src/app/spec_coverage/main.spl"
+            | "src/app/spl_coverage/main.spl"
             | "src/app/replay/main.spl"
```

(in `fn app_receives_user_args_only`'s `matches!` list, main.rs ~line 1400).
This second list controls argv shape: apps in it receive `args.iter().skip(1)`
(i.e. `["status"]`, not `["spl-coverage","status"]`) — confirmed correct for
`src/app/spl_coverage/main.spl`'s `main()`, which calls `get_cli_args()` and
reads `filtered_args[0]` as the subcommand name (`dump`/`status`/`clear`),
exactly the same shape `spec_coverage/main.spl` expects.

### Verification (maps to gate script row `prereq3_spl_coverage_dispatchable`) — gate script itself needs a companion fix

**The gate script's existing probe will NOT go green from diffs 1-3 alone,
even once they are correctly applied — read `src/app/spl_coverage/main.spl`'s
`cmd_status()` (lines ~63-77) before assuming otherwise.** `cmd_status()`
returns `1` whenever `coverage_enabled()` is false — i.e. whenever
`SIMPLE_COVERAGE` is not set in the probing process's environment, which is
exactly the gate script's current probe: `p3_out=$("$BIN" spl-coverage status
2>&1)` with no `SIMPLE_COVERAGE` set. The gate script's own success condition
is `[ "$p3_rc" -eq 0 ]` — so a *correctly wired* `spl-coverage status` still
returns rc=1 by design (coverage genuinely is disabled for that bare
invocation) and the row stays UNMET.

This is a real gap in the gate script, not in the CLI's design (returning
non-zero for "coverage tracking is disabled" is reasonable status-command
behavior). The bootstrap session should patch
`scripts/check/check-render2d-coverage.shs`'s prereq-3 probe to either (a)
set `SIMPLE_COVERAGE=1` before the probe call, since the check is "is the
subcommand dispatchable," not "is coverage currently enabled," or (b) treat
absence of the `file not found: spl-coverage` string as sufficient (current
`elif`/`else` structure already does this as a secondary check but the
primary branch requires rc=0 first). Simplest fix, mirroring option (a):

```diff
-p3_out=$("$BIN" spl-coverage status 2>&1)
+p3_out=$(SIMPLE_COVERAGE=1 "$BIN" spl-coverage status 2>&1)
 p3_rc=$?
```

With that gate-script change, once diffs 1-3 land, `spl-coverage status`
under `SIMPLE_COVERAGE=1` hits the `if coverage_enabled():` branch in
`cmd_status()` and returns 0. Without either the CLI diffs or the gate-script
change, this row cannot go MET — both sides are required.

### Dependency note

This prerequisite is self-contained — it does not depend on 1, 2, 4, or 5, and
should land first since it's the smallest, most mechanical diff and turns the
gate script from 5/5 UNMET to 4/5 UNMET as an early, verifiable signal that
the patch-prep methodology works before tackling the harder Rust MIR/runner
changes.

---

## Prerequisite 1: real source spans at decision-probe call sites

### Root cause, precisely located (path corrected from the bug doc)

File: `src/compiler_rust/compiler/src/interpreter_control.rs` (bug doc's path
`interpreter_call/core/interpreter_control.rs` does not exist in this tree —
verified by `ls`). Six call sites hardcode the literal string `"<source>"` as
the file identity passed to `record_decision_coverage_sffi`:

```
279:        record_decision_coverage_sffi("<source>", if_stmt.span.line, if_stmt.span.column, decision_result);
317:            record_decision_coverage_sffi("<source>", if_stmt.span.line + idx, if_stmt.span.column, elif_decision);
444:                        "<source>",
485:                "<source>",
517:            "<source>",
4742:                "<source>",
```

(Line numbers 444/485/517/4742 are within the multi-line call — the literal
appears as the first positional arg on its own line; re-verified against the
current tree, and differ from the bug doc's 443/484/516/4741 by exactly one
line each, consistent with a one-line drift since 2026-08-07's earlier read,
not a different set of call sites.)

### Proposed diff — thread real file identity through

The exact replacement text cannot be written blind: each of these six call
sites is inside a different method with different local context, and it is
not yet established (without reading ~200 lines of surrounding code per site)
what variable — if any — already holds the current source file path in that
scope (an interpreter frame field? a module-level `self.current_file`? an
argument threaded from the caller?). Two of the six sites (444, 485, 517) are
close together (lines 420-520) and may share one local; site 4742 is far away
in a different function and needs independent inspection.

**This is why this doc records the diff shape, not literal before/after
text, for prerequisite 1** — see "risks and unknowns" below. The shape every
site needs:

```diff
-        record_decision_coverage_sffi("<source>", if_stmt.span.line, if_stmt.span.column, decision_result);
+        record_decision_coverage_sffi(self.current_source_file(), if_stmt.span.line, if_stmt.span.column, decision_result);
```

where `self.current_source_file()` is a placeholder for whatever accessor the
bootstrap session determines actually holds the real path in each of the six
scopes (likely not identical across all six — the interpreter may be
mid-call into an imported module at some sites, so "the file currently
executing" is not a single fixed string for the whole run).

### Verification (maps to gate script row `prereq1_real_source_spans_UNVERIFIED_BY_SCRIPT`)

The gate script currently records this row as unconditionally unmet — it has
no mechanical probe. The bootstrap session should extend the gate script (or
run manually first) with:

```
grep -n '"<source>"' src/compiler_rust/compiler/src/interpreter_control.rs
```

Zero matches = prerequisite met (mechanically verifiable — the literal string
is a reliable proxy for "not yet fixed"). Additionally, a runtime check: run
a spec with `SIMPLE_COVERAGE=1`, dump coverage via `bin/simple spl-coverage
dump` (once prerequisite 3 lands) or `rt_coverage_dump_sdn()`, and confirm the
emitted records carry the real `.spl` file path, not `<source>`.

### Dependency note

Independent of 2-5. Can land in parallel with prerequisite 3. Should land
before prerequisite 5 (rollup), since a rollup keyed on `<source>` cannot
produce a real per-file table regardless of what else is fixed.

---

## Prerequisite 2: production MIR lowering must honor coverage — more nuanced than the bug doc states

### What the bug doc claimed vs. what is actually true

The bug doc states production MIR lowering "never calls" the
coverage-instrumented lowering path and that only Rust unit tests reach it.
**This is only true for one of the three lowering branches.** Re-reading the
current tree:

1. `src/compiler_rust/compiler/src/pipeline/execution.rs:993` — inside the
   `bootstrap_mode` branch (`SIMPLE_BOOTSTRAP=1`) — does call the plain
   `crate::mir::lower_to_mir(&hir)`, confirming the bug doc's claim **for
   that branch only**. Anchor text at that line:
   `crate::mir::lower_to_mir(&hir).map_err(|e| crate::error::factory::mir_lowering_failed(&e))?`

2. The non-bootstrap production path (`type_check_and_lower_with_context_and_project_hint`
   → `process_hir_to_mir`, `src/compiler_rust/compiler/src/pipeline/lowering.rs:1698-1699`)
   **already calls** `mir::lower_to_mir_full(&hir_module, self.contract_mode,
   di_config, self.coverage_enabled)` — i.e. it already threads a
   `coverage_enabled` flag into MIR lowering, contradicting the bug doc's
   blanket claim that only Rust unit tests reach coverage-aware lowering.

3. **The real gap is upstream of both branches**: `self.coverage_enabled`
   (the `CompilerPipeline` struct field consumed at lowering.rs:1698, default
   `false`, declared `src/compiler_rust/compiler/src/pipeline/core.rs:47`) is
   only ever set to `true` via `set_coverage_enabled()`
   (`pipeline/core.rs:255-257`), which is called from exactly two places in
   the non-test tree: `driver/src/exec_core.rs:564`, gated on
   `options: &crate::CompileOptions` having `.coverage == true` — an explicit
   AOT/SMF `compile_file_with_options` path — and nowhere else in production
   code. **Grepping all of `pipeline/*.rs` for `SIMPLE_COVERAGE` finds zero
   reads** — `self.coverage_enabled` is never auto-derived from the
   `SIMPLE_COVERAGE` env var or from the global `is_coverage_enabled()`
   helper (`src/compiler_rust/compiler/src/coverage.rs:297`,
   `if std::env::var("SIMPLE_COVERAGE").is_ok()`) that the interpreter and
   native codegen backend (`pipeline/codegen.rs:31`,
   `let coverage_enabled = crate::coverage::is_coverage_enabled();`) both
   already use. So: `bin/simple test <spec> --coverage`, which sets
   `SIMPLE_COVERAGE=1` (via `test_runner/runner.rs`'s `initialize_coverage`,
   see prerequisite 4 below) never reaches `set_coverage_enabled(true)` on
   the `CompilerPipeline` used for that compile, so MIR-level `DecisionProbe`
   emission stays off for the `bin/simple test` path specifically, even
   though the interpreter's own (currently-`<source>`-tagged) decision
   recording and the native codegen backend's coverage flag both DO respond
   to the env var through the separate `is_coverage_enabled()` global.

### Proposed diff — thread the env var through where the AOT flag doesn't reach

File: `src/compiler_rust/compiler/src/pipeline/lowering.rs`, in
`process_hir_to_mir` immediately before the `lower_to_mir_full` call
(anchor: `let di_config = self.project.as_ref().and_then(|p| p.di_config.clone());`,
currently line 1697):

```diff
         // Lower HIR to MIR with contract mode, DI config, and coverage (#674)
         let di_config = self.project.as_ref().and_then(|p| p.di_config.clone());
-        let mut mir_module = mir::lower_to_mir_full(&hir_module, self.contract_mode, di_config, self.coverage_enabled)
+        let coverage_enabled = self.coverage_enabled || crate::coverage::is_coverage_enabled();
+        let mut mir_module = mir::lower_to_mir_full(&hir_module, self.contract_mode, di_config, coverage_enabled)
             .map_err(|e| crate::error::factory::mir_lowering_failed(&e))?;
```

This makes the field-based flag (`--coverage` on the AOT path) and the
env-var-based flag (`SIMPLE_COVERAGE=1` on the test/interpreter path) both
enable MIR-level probe emission, matching how `pipeline/codegen.rs:31`
already resolves the same question for native codegen. The bootstrap-mode
branch (execution.rs:993) should get an analogous change if the bootstrap
lane's own coverage matters — flagged as unconfirmed scope below.

**Ordering check performed, not left open:** `crate::coverage::is_coverage_enabled()`
reads `GLOBAL_COVERAGE.get().is_some()` (coverage.rs:302-304) — true only
after `init_coverage()`/`init_coverage_from_env()` has actually run in that
process, not merely from the env var's presence. Confirmed by direct read:
`init_coverage_from_env()` is called at `src/compiler_rust/driver/src/main.rs:1095`,
unconditionally, as the second statement inside `fn real_main()` (starts line
1090) — i.e. before argument dispatch, before any compile. So for any process
whose `SIMPLE_COVERAGE` env var is set at process start (including a child
spawned by `process_run`/`process_run_bounded`, which inherit parent env by
default), `is_coverage_enabled()` will already be `true` by the time this
diff's `process_hir_to_mir` runs later in the same process. This closes what
would otherwise be an ordering risk — no known counter-scenario found.

### Verification (maps to gate script row `prereq2_production_mir_coverage_lowering_UNVERIFIED_BY_SCRIPT`)

No mechanical probe exists today. The bootstrap session should add one:
either (a) a Rust unit test asserting `lower_to_mir_full` receives
`coverage_enabled == true` when `SIMPLE_COVERAGE=1` is set and
`self.coverage_enabled` is false, or (b) an end-to-end probe: run a spec with
a real branch under `SIMPLE_COVERAGE=1 bin/simple test <spec> --coverage`,
inspect the MIR emitted via `--emit-mir` for `DecisionProbe` instructions
that were previously absent.

### Dependency note

Should land after prerequisite 1 conceptually (spans should be real before
volume of probes increases), but there's no hard code dependency — they touch
different files and can land in either order or in parallel. Must land before
prerequisite 5 (rollup) has anything real to aggregate for JIT/native, since
today those probes are simply never emitted for the `bin/simple test` path.

---

## Prerequisite 4: coverage export must fire on the spipe/.spl runner path

### Root cause, precisely located — corrected and sharpened from the bug doc

The bug doc correctly identifies that `save_coverage_data`
(`src/compiler_rust/driver/src/cli/test_runner/coverage.rs:8`, called from
`runner.rs:434`) is the working Rust-side export call, and correctly observes
it doesn't fire on the actual `bin/simple test <spec>` invocation. Tracing
**why**, precisely:

1. `bin/simple test <spec.spl>` with default args (interpreter mode) matches
   `test_should_use_light_daemon_client` in
   `src/compiler_rust/driver/src/main.rs` (~line 195), so `dispatch_command`
   routes to the **pure-Simple** app
   `src/app/test_runner_new/test_runner_client.spl`, not to the Rust
   `handle_test_rust` → `runner.rs::run_tests` → `save_coverage_data` chain
   at all.
2. Inside `test_runner_client.spl`, when `SIMPLE_COVERAGE` is set,
   `cov_bypass` is true (line 369: `val cov_bypass = cov_env != "" and
   cov_env != "0"`), which forces `daemon_ok = false` (line 394) and takes
   the **direct lane**: `run_one_direct(binary, p, run.timeout_secs)` (line
   420, function defined at line 238).
3. `run_one_direct` (`test_runner_client.spl:238-251`) spawns a **child
   process**: `binary ["test", "--no-session-daemon", "--timeout", N, path]`
   (line 243). Passing `--no-session-daemon` makes the CHILD's own
   `dispatch_command` match `test_should_use_single_runner` (main.rs ~line
   189: `args.iter().skip(1).any(|arg| arg == "--no-session-daemon")`), which
   routes the child to **yet another pure-Simple app**,
   `src/app/test_runner_new/test_runner_single.spl` — never the Rust
   `run_tests`/`save_coverage_data` chain either.
4. `test_runner_single.spl` **does** implement its own line-coverage
   mechanism (confirmed working, matches the empirically observed `coverage:
   <path> NN% (X/Y lines)` stdout banners): it injects an epilogue into the
   executed spec copy that prints `rt_coverage_dump_sdn()` between sentinel
   markers `__SIMPLE_COV_SDN_BEGIN__`/`__SIMPLE_COV_SDN_END__`
   (`_cov_instrument_for_coverage`, lines 431-452), then parses that region
   back out of the child's stdout (`_cov_split_output`, lines 454-470,
   invoked at line 813: `val (cov_clean, cov_extracted) =
   _cov_split_output(stdout)`, with the extracted SDN text landing in
   `cov_sdn` at line 815). **This is exactly the working half of the
   primitive** — but `cov_sdn` at that point is only ever used to compute and
   print the percentage banner; grepping the whole file for
   `SIMPLE_COVERAGE_OUTPUT` and `rt_file_write_text` shows the extern is
   imported (line 33) and used elsewhere for tmp-copy bookkeeping, but
   **never** to persist `cov_sdn` to the path in `SIMPLE_COVERAGE_OUTPUT`.
   That is the precise, single missing statement.

### Proposed diff — write `cov_sdn` to `SIMPLE_COVERAGE_OUTPUT` when set

File: `src/app/test_runner_new/test_runner_single.spl`, immediately after
line 815 (anchor: `cov_sdn = cov_extracted`):

```diff
     var child_stdout = stdout
     var cov_sdn = ""
     if cov_on:
         val (cov_clean, cov_extracted) = _cov_split_output(stdout)
         child_stdout = cov_clean
         cov_sdn = cov_extracted
+        val cov_output_path = env_get("SIMPLE_COVERAGE_OUTPUT") ?? ""
+        if cov_output_path != "" and cov_sdn != "":
+            val _ = rt_file_write_text(cov_output_path, cov_sdn)
     if child_stdout != "":
         print child_stdout
```

`env_get` is already imported (line 27: `use app.io.mod.{env_get}`) and
`rt_file_write_text` is already declared `extern` (line 33) — both usable
with zero new imports.

**Multi-file caveat (flagged, not resolved here):** when the outer
`test_runner_client.spl` invocation names more than one spec path, each
child `run_one_direct` call gets its own `SIMPLE_COVERAGE_OUTPUT` env var
value (inherited unchanged from the parent), so N specs would each overwrite
the same output path with only their own SDN, the last writer winning silently.
The gate script's own probe (prereq 4) only ever passes a single spec, so this
diff satisfies that specific probe; whether multi-spec aggregation is in scope
for U1.3's acceptance is a plan-level question, not resolved by this patch-prep
doc — see "risks and unknowns."

### Verification (maps to gate script row `prereq4_artifact_export`)

Exactly what the gate script already does — no gate-script change needed:

```
ARTIFACT=$(mktemp -u /tmp/probe.XXXXXX.sdn); rm -f "$ARTIFACT"
SIMPLE_COVERAGE=1 SIMPLE_COVERAGE_OUTPUT="$ARTIFACT" \
    bin/simple test test/01_unit/lib/common/gpu/engine2d/scalar_oracle_spec.spl --coverage --no-cache
test -s "$ARTIFACT" && echo MET || echo UNMET
```

### Dependency note

Independent of 1, 2, 3. Should land after prerequisite 1 if the goal is a
*meaningful* artifact (today `cov_sdn` still carries `<source>`-tagged
records for anything that goes through `interpreter_control.rs`'s decision
recording, so the exported file would be non-empty but not per-file
attributable until prerequisite 1 also lands) — but the gate script's
prerequisite 4 row only checks non-emptiness, so this diff alone flips that
row MET even before prerequisite 1 lands. Flag this gap explicitly if
landing 4 before 1: the gate goes green on a row whose *content* is still
not real per-file data.

---

## Prerequisite 5: per-file/per-module rollup

### Status: new code, not a location fix — least pinned of the five

No existing function aggregates raw decision events into a per-file or
per-module hit/total table; this is why the bug doc calls it "new code, not a
configuration fix." This patch-prep doc does not propose a diff for
prerequisite 5, for two reasons: (a) it is genuinely new code rather than a
located bug, so there is no existing anchor line to diff against, and (b) its
correct shape depends on the *output* of prerequisites 1 and 4 — a rollup
built against `<source>`-tagged, non-exported records would need to be
rewritten once real file identity and export exist, wasting the work. Once 1
and 4 land, the natural location is inside
`src/app/spl_coverage/main.spl` (which already has `dump`/`status`/`clear`
subcommands and imports `coverage_dump_sdn`/`coverage_enabled` — a `report`
or extended `status` subcommand that parses the dumped SDN into a per-file
table is the natural next subcommand once prerequisite 3 makes the CLI
reachable at all).

### Verification (maps to gate script row `prereq5_perfile_rollup_UNVERIFIED_BY_SCRIPT`)

No mechanical probe exists; the bootstrap session should design one only
after 1 and 4 land and the rollup's actual output shape is known.

### Dependency note

**Must land last** — it depends on real spans (1) and a real, exported
artifact (4) to have meaningful input; building it against today's
`<source>`/unexported records would need a rewrite.

---

## Ordering summary

```
3 (spl-coverage CLI wiring)  — independent, land first (cheapest, most mechanical)
1 (real source spans)        — independent, land in parallel with 3
2 (MIR coverage threading)   — independent, land in parallel with 3/1
4 (export to SIMPLE_COVERAGE_OUTPUT) — independent, land in parallel; artifact
                                        is non-empty before 1 lands but not
                                        yet per-file-meaningful until 1 lands
5 (rollup)                   — LAST; depends on 1 and 4 being real, not just present
```

None of 1-4 has a hard *code* dependency on any other (they touch disjoint
files), so they could in principle be four separate small commits landed in
any order — the ordering above is about when the *result* becomes
meaningful, not about compile-time dependency.

---

## Risks and unknowns (explicit — do not treat as resolved)

0. **A full Rust-seed rebuild is currently documented as BLOCKED in this
   repo, independent of anything in this doc.** `.claude/rules/bootstrap.md`'s
   "KNOWN BLOCKER (2026-08-06)" section states `scripts/bootstrap/bootstrap-from-scratch.sh
   --full-bootstrap --deploy` — the correct, documented command for a change
   that touches `src/compiler_rust/**` (which prerequisites 2 and 3-diffs-1/3
   do) — currently fails at Stage 3 with `unresolved type: ByteOrder` in
   `cache_validator.spl`, and then an `Effect` facade collision. This may or
   may not still be true by the time the bootstrap session runs (re-check the
   bug doc it cites,
   `doc/08_tracking/bug/t3_full_bootstrap_stage3_unresolved_type_byteorder_cache_validator_2026-08-06.md`,
   for current status first) — but the bootstrap session must not assume a
   plain `--full-bootstrap --deploy` will succeed without checking. **Do not
   hand-roll `cargo build --release` + manual copy to `bin/release/<triple>/simple`**
   as a workaround — bootstrap.md explicitly flags that as producing an
   unbanered *seed* masquerading as the self-hosted binary, which several
   sessions have already done by mistake in this same tree.
1. **Prerequisite 1's actual fix text is unverified.** This doc could not
   determine, without reading ~150-250 lines of surrounding interpreter
   context per call site, what expression already holds "the real current
   source file" at each of the six sites (279, 317, 444, 485, 517, 4742). It
   may not be a single uniform accessor — the interpreter could be mid-call
   into an imported module at some of these sites, in which case "the file
   currently executing" is call-stack-dependent, not a single field. The
   bootstrap session must read each site's enclosing function before writing
   the real diff.
2. **Whether the bootstrap-mode branch (execution.rs:993) needs the same
   coverage threading as prerequisite 2's fix is unconfirmed.** `SIMPLE_BOOTSTRAP=1`
   is a rare, explicit self-hosting flag; whether any coverage plan needs
   that lane instrumented is a scope question this doc does not answer.
3. **The multi-spec `SIMPLE_COVERAGE_OUTPUT` overwrite behavior in prerequisite
   4's diff is a known gap, not a fixed one.** Whether U1.3's acceptance
   criteria require multi-spec aggregation (append vs. overwrite) was not
   determined from the plan doc text available; flag to the bootstrap session
   to check the plan's exact acceptance wording before deciding whether a
   single `test -s "$ARTIFACT"` check is a sufficient bar or whether the gate
   script itself needs a multi-file variant.
4. **None of these five diffs have been compiled or run.** Every line number
   and anchor text was re-verified by direct source read on 2026-08-07 against
   the working tree, but Rust type-checking (borrow rules, trait bounds on
   `self.coverage_enabled || crate::coverage::is_coverage_enabled()`, whether
   `CompilerPipeline` has `crate::coverage` in scope at that point) is
   unverified without a build. The `.spl` diff (prerequisite 4) is lower-risk
   syntactically (both `env_get` and `rt_file_write_text` are already used
   elsewhere in the same file) but is equally unbuilt.
5. **Whether `self.coverage_enabled` being true also needs to reach the
   bootstrap-mode branch or the bare `type_check_and_lower` (no-context)
   branch** (`pipeline/lowering.rs:1741-1758`, used when `source_path` is
   `None`) was not traced — that branch calls `self.process_hir_to_mir(hir_module)`
   too, so it likely inherits the same fix automatically since
   `process_hir_to_mir` is the single shared function being patched. This
   should hold but was not independently traced end-to-end for that branch's
   callers.
6. **Whether `bin/simple test --coverage` on a *native/compiled* mode spec
   (not the default interpreter mode) reaches the same `test_runner_client.spl`
   path or a different one** was not traced. This doc's evidence trail (steps
   1-4 under prerequisite 4) is for the *interpreter*-mode default; a
   `--compile`/native-mode test run may dispatch differently and would need
   separate tracing before claiming the same fix covers it.

---

## Exact command sequence for the bootstrap session

**Disk-safety precondition — check before building:**

```
df -h /home/ormastes/dev/pub/simple
```

Confirm free space is comfortably above the ~130G+ this tree's
`src/compiler_rust/target` has been observed to consume for a fresh build
(126G measured for the existing target dir alone, plus headroom for a second
parallel build artifact set if working in a worktree). Do not proceed if free
space is anywhere near that figure; this repo has been ENOSPC-wiped to
near-zero files twice, both times from insufficient headroom during a Rust
build.

**Isolated worktree + build + verify:**

**Read risk item 0 above FIRST** — a plain `bin/simple build bootstrap` will
either not exist as a working command in a fresh worktree (a freshly
`git worktree add`-ed checkout has no deployed `bin/release/<triple>/simple`
at all — that path is gitignored) or, once you locate the correct rebuild
entrypoint, may hit the documented Stage 3 self-host blocker. Do not treat
either failure as this doc's diffs being wrong; diagnose which layer failed
before concluding anything about prerequisites 1-4.

```sh
cd /home/ormastes/dev/pub/simple
df -h .                                   # confirm headroom per above — STOP if tight
git worktree add /tmp/u13-bootstrap-wt -b u13-coverage-primitive origin/main
cd /tmp/u13-bootstrap-wt
sh scripts/setup/setup.shs                # create bin/simple symlink for this worktree

# Apply the five diffs from this doc (prerequisites 3 [three sub-diffs], 1,
# 2, 4; skip 5 — no diff proposed, new code to design separately) by hand,
# reading each anchor's current surrounding context first (line numbers WILL
# have drifted since 2026-08-07). Also apply the gate-script companion diff
# under prerequisite 3's verification section.

# Prerequisites 2 and 3 touch src/compiler_rust/** (Rust seed source), so a
# pure-Simple-only `--mode=dynload` rebuild is NOT sufficient — those changes
# require the Rust seed itself to be recompiled via --full-bootstrap. Check
# risk item 0 first; if Stage 3 is still blocked, this cannot complete until
# that separate, pre-existing blocker is fixed or worked around.
scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy

# Re-run the gate script (with its prerequisite-3 SIMPLE_COVERAGE=1 fix
# applied, and extended for prerequisites 1/2/5 per this doc's Verification
# sections).
sh scripts/check/check-render2d-coverage.shs
```

**PASS is not achievable from diffs 1-4 alone — this is expected, not a
failure of this doc.** The gate script hardcodes prerequisites 1, 2, and 5 as
UNMET unconditionally by design (see the script's own header comment) until
it is extended with mechanical checks for them. Landing only diffs
1/2/3/4 (and their gate-script companion fix) moves the verdict from `FAIL —
5 prerequisite(s) checked, 5 unmet` to `FAIL — 5 prerequisite(s) checked, 2
unmet` (1 and 2 mechanically verified MET via the greps in their
"Verification" sections above; 5 still hardcoded UNMET since no rollup exists
yet). Extending the gate script to actually check 1, 2, and 5 mechanically,
and then building prerequisite 5 itself, are both required before a true
`PASS` line is possible:

```
check-render2d-coverage: prerequisite detail:
  [MET] prereq3_spl_coverage_dispatchable -- bin/simple spl-coverage status exited 0
  [MET] prereq4_artifact_export -- artifact written and non-empty at ...
  [MET] prereq1_real_source_spans... (once the script is extended per this doc)
  [MET] prereq2_production_mir_coverage_lowering... (once the script is extended)
  [MET] prereq5_perfile_rollup... (once designed and the script is extended)
check-render2d-coverage: PASS — 5 prerequisite(s) checked, all met (branch-coverage % may be reported)
```

**Cleanup:**

```sh
cd /home/ormastes/dev/pub/simple
git worktree remove /tmp/u13-bootstrap-wt
```
