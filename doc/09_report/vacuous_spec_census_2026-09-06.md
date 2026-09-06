# Vacuous Spec Census — specs that shell out to the CLI and inherit the runner's forced interpret lane

Date: 2026-09-06
Host: aarch64 Linux, 20 cores, 121 GiB RAM
Binary under test: `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`
(50,093,192 bytes, mtime 2026-09-06 09:59:11 +0900) — the **Rust seed**, which
announces itself as `WARNING: this Rust-built Simple binary is a bootstrap seed only`.
Worktree: `.claude/worktrees/agent-a8e81af98f1a7ff42`, branch `work/vacuous-spec-census-2026-09-06`.

Nothing in `test/` or `src/` was modified by this census. It is static analysis
plus disposable fixtures under `build/vsc/` (gitignored). No spec, `it` block,
TODO or feature was deleted, weakened or reworded.

---

## 1. The mechanism, verified

### 1.1 Where the runner pins the lane

Two runners set both variables in the spec process:

```
src/app/test_runner_new/test_runner_single.spl:1089   env_set("SIMPLE_RUNTIME_MODE", "interpreter")
src/app/test_runner_new/test_runner_single.spl:1090   env_set("SIMPLE_EXECUTION_MODE", "interpret")
src/lib/nogc_sync_mut/test_runner/test_runner_single.spl:169-170   (same pair)
src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl:213      env_set("SIMPLE_EXECUTION_MODE", "interpret")
```

`test_runner_execute.spl:209-212` states the intent — the child `run <file>` must
be interpreted so the BDD intrinsics (`describe`/`it`/`expect`) load. That is
correct for the *spec* process. The defect is that it also reaches every
**grandchild** the spec spawns.

The seed reads the variable in `ExecCore::with_gc_and_provider`
(`src/compiler_rust/driver/src/exec_core.rs:223-232`), defaulting to
`ExecutionMode::Jit` when unset:

```rust
let mode = match std::env::var("SIMPLE_EXECUTION_MODE") {
    Ok(s) => match ExecutionMode::parse_str_checked(&s) { ... },
    Err(_) => ExecutionMode::Jit, // JIT default (Stage 2+)
};
```

`SIMPLE_RUNTIME_MODE` has **no reader** anywhere in `src/compiler_rust/driver/`;
it is read only by `.spl` code (`src/lib/nogc_sync_mut/spec.spl:184-207`,
`lsp/parser_adapter.spl:59`, `common/encoding/font_registry.spl:566`).
`SIMPLE_EXECUTION_MODE` is the operative one for the seed.

An in-repo session already found and documented this at
`test/03_system/app/mem_cli_spec.spl:126-140`, which is why that spec is one of
the very few that scrubs:

> "`bin/simple test` sets both to force the tree-walk interpreter for the spec
> process tree, and `Command::spawn()` inherits the full parent environment, so
> without this the fixture inherits interpreter mode too."

### 1.2 Demonstrated, both directions

Fixture `build/vsc/child.spl` prints its own two variables.

| invocation | `SIMPLE_EXECUTION_MODE` seen by child |
|---|---|
| `bin/simple run build/vsc/child.spl` from a clean shell | `[]` (unset ⇒ JIT default) |
| `rt_process_run("bin/simple", ["run", child])` from inside a spec run by `bin/simple test` | `[interpret]`, `SIMPLE_RUNTIME_MODE=[interpreter]` |
| same, wrapped in `env -u SIMPLE_EXECUTION_MODE -u SIMPLE_RUNTIME_MODE` | `[]` — default restored |

Both spec-side runs reported `Results: 1 total, 1 passed, 0 failed`, i.e. the
lane shift is completely silent.

### 1.3 Engine oracle — the lane really differs

Printing the variable only proves inheritance. To prove the *engine* differs, a
second fixture (`build/vsc/child2.spl`) calls `rt_signal_install`, which is a
registered runtime symbol for JIT/native codegen but is **not** in the
interpreter's extern dispatch table:

| invocation | result |
|---|---|
| `run child2.spl`, clean shell | `LANE_ORACLE_rt_signal_install=1` (JIT) |
| `run child2.spl`, `SIMPLE_EXECUTION_MODE=interpret` | `error: semantic: unknown extern function: rt_signal_install` |
| `run child2.spl`, `SIMPLE_EXECUTION_MODE=jit` | `LANE_ORACLE_rt_signal_install=1` |

### 1.4 Which subcommands are lane-sensitive — measured, not assumed

This is the fact that decides most of the census, so it was measured rather than
inferred.

**All three subcommands *read* the variable** (a bogus value exits 2 from
`parse_str_checked`):

```
run          mode=bogus_lane_xyz  rc=2  error: unknown SIMPLE_EXECUTION_MODE="bogus_lane_xyz"
compile      mode=bogus_lane_xyz  rc=2  (same)
native-build mode=bogus_lane_xyz  rc=2  (same)
```

But reading it is not the same as being changed by it:

- **`compile` (SMF) is lane-INDEPENDENT.** Two `compile` runs in the *same* env
  differ at 76 byte offsets (the output is nondeterministic); an unset-vs-interpret
  pair differs at the **identical 76 offsets** (`offsets_identical=YES`,
  `build/vsc/census/cmp_offsets.sh`). The lane changes nothing in the artifact.
- **`compile --native` is lane-INDEPENDENT for the artifact.** Built under
  `SIMPLE_EXECUTION_MODE=interpret` (rc=0, 437,064-byte ELF), the resulting ELF
  prints `LANE_ORACLE_rt_signal_install=1` when executed — from a clean shell
  **and** with `SIMPLE_EXECUTION_MODE=interpret` still set. A native artifact is
  genuinely native regardless of the compiler's own lane, and executing it is
  immune to the variable.
- **`run` is lane-SENSITIVE.** §1.3.
- **`native-build`**: could not be exercised on this host (`native-build worker
  exited with code 1` for both lanes on a hello-world fixture). Treated as
  lane-independent-for-the-artifact by analogy with `compile --native`, and any
  spec resting on that alone is called out as such.

### 1.5 `--mode=native` is not a lane selector — the seed only recognises `interpreter`

`src/compiler_rust/driver/src/main.rs:255-270` is the whole of the driver's
`--mode` handling on the `run` path:

```rust
if arg == "--mode" && i + 1 < args.len() { return args[i + 1] == "interpreter"; }
if let Some(mode) = arg.strip_prefix("--mode=") { return mode == "interpreter"; }
```

It answers one question — "is interpreter requested?" — and nothing else.
`--mode=native` therefore selects nothing; the lane comes from the environment.
Replayed directly:

| invocation | result |
|---|---|
| `run child2.spl --mode=native --force-rebuild --clean`, env=`interpret` | `unknown extern function: rt_signal_install` → **interpreter** |
| same, clean shell | `LANE_ORACLE_rt_signal_install=1` → JIT |
| `run --mode=native child2.spl` (flag before path) | `error: io: Cannot read "--mode=native"` — the flag is taken as the file |

This is the exact invocation shape used by
`test/03_system/feature/language/host_gpu_lane_spec.spl:151`.

---

## 2. Method

Population: every `*_spec.spl` under `test/` — **23,162 files** (the tree carries
duplicated `test/01_unit` ↔ `test/unit`, `test/02_integration` ↔ `test/integration`,
`test/03_system` ↔ `test/system` mirrors, so a deduped figure is given alongside
every raw count).

Spawn idioms were **discovered, not assumed.** Enumerating `rt_process_*` uses
under `test/` gave, by frequency: `rt_process_run` (2201), `rt_process_run_timeout`
(656), `rt_process_spawn_async` (46), `rt_process_spawn_piped` (31),
`rt_process_run_bounded` (16), `rt_process_run_capture` (9),
`rt_process_spawn_guarded` (8), `rt_process_run_inherit` (5), `rt_process_exec` (4);
plus the `.spl`-level wrappers `process_run`, `process_spawn_async`, `shell(...)`,
`shell_exec`, `run_command`, `exec_capture`. `shell("…")` string form matters —
several specs build a whole `sh -c` line with the binary embedded in it.

Detection (`build/vsc/census/site4.awk`), per file, over **comment-stripped** lines
(a leading-`#` line is never evidence — a raw `bin/simple` grep hits 3,174 files,
overwhelmingly prose):

```
SPAWN = (rt_process_run|rt_process_spawn|rt_process_exec|rt_process_output|process_run
        |process_spawn|process_exec|run_command|shell_exec|shell[(]|run_shell
        |exec_capture|rt_system|system_run)
BIN   = (bin/simple|bin/release/<triple>/simple|bootstrap/stage<n>/simple
        |find_simple_binary|simple_binary|simple_bin|dispatch_binary|SIMPLE_BIN)
```

A **site** is a SPAWN line whose 5-line window also matches BIN (multi-line
argument arrays are common). The window is then scanned for the subcommand
(`run` / `compile` / `native-build` / `test` / `build`, else `unknown`).

**Lane declaration is detected at FILE level, not window level.** Window-level
detection was tried first and under-counted, for two concrete reasons now used as
the regression cases for the rule:

- `test/01_unit/app/cli/run_semantic_error_exit_code_spec.spl` sets the mode at
  the *call* site (`run_engine("SIMPLE_EXECUTION_MODE=jit", BAD)`, lines 48-83),
  while the spawn at line 33 only interpolates `{engine_env}`.
- `test/01_unit/lib/common/crypto/sha3_jit_engine_divergence_spec.spl:32` builds it
  by concatenation: `process_run("env", ["SIMPLE_EXECUTION_MODE=" + mode, "bin/simple", "run", PROBE])`.

Both are genuinely immune and both were initially misfiled as vacuous. The
file-level rule flags any code line containing `SIMPLE_EXECUTION_MODE=`,
`SIMPLE_RUNTIME_MODE=`, `"SIMPLE_EXECUTION_MODE", "`, `"-u", "SIMPLE_…_MODE"`,
`env -u SIMPLE_…_MODE`, `engine_probe`, `run_in_modes` or `ModeRunner`.

Native/JIT **intent** heuristic (path, or a `describe`/`it`/`slow_it` string):
`native|codegen|jit|llvm|mir|cranelift|backend|hwir|aot|machine code|object file|sigsegv|miscompil`.
This is a triage filter for hand review, not a verdict.

Every file the heuristic surfaced was then **read by hand** (spawn lines plus
`it` names, `build/vsc/census/handcheck.txt`), and the hand verdict overrides the
heuristic in both directions.

---

## 3. Counts

**572 spec files shell out to the Simple CLI** (415 after collapsing the mirror
trees), across **1,050 spawn sites**. That is 2.5% of the 23,162 spec files.

| class | raw | deduped | basis |
|---|---|---|---|
| IMMUNE — explicit lane declaration | 20 | 19 | file sets or unsets `SIMPLE_EXECUTION_MODE`, or uses `engine_probe`/`ModeRunner` |
| IMMUNE — AOT artifact | 23 | 19 | spawns `native-build`/`compile --native`; the lane cannot reach the artifact (§1.4) |
| IMMUNE — lane-independent subcommand | 33 | 26 | only `compile`/`test`/`build` sites |
| **LANE_SHIFTED_RUN** | **370** | **245** | ≥1 unscrubbed `run` spawn — the child is forced onto the interpreter |
| UNCLEAR — subcommand not determinable | 126 | 107 | spawn + binary token, subcommand built dynamically or spawn is a string assertion |
| **total** | **572** | **415** | |

The per-class deduped column sums to 416, one more than the deduped total of 415:
exactly one mirror pair has its two copies in different classes, so collapsing
the pair inside a class does not collapse it across classes. Not an arithmetic
error.

Subcommand distribution across the 1,050 sites: `run` 533, `unknown` 321,
`compile` 89, `test` 73, `native-build` 20, `build` 2, plus 12 mixed sites.
Only **28 of 1,050 sites** sit in a file that declares a lane.

### 3.1 The LANE_SHIFTED_RUN 370, resolved

The intent heuristic split the 370 into 29 native-intent candidates and 341
others. All 29 were read by hand:

**VACUOUS — hand-verified (4 paths, 3 distinct specs across the mirror trees):**

| spec | site | current status | why |
|---|---|---|---|
| `test/03_system/feature/language/host_gpu_lane_spec.spl` | `:151` `rt_process_run(simple_binary(), ["run", path, "--mode=native", "--force-rebuild", "--clean"])` | **unknown** | `it "should emit native runtime queue evidence for a GPU lane"`. Proven by direct replay (§1.5): this exact shape lands on the **interpreter** under an inherited `interpret`, and `--mode=native` is not a lane selector in the seed at all. The spec asks for native evidence and is guaranteed not to get it. |
| `test/03_system/lib/gpu/object_vm/gpu_mmu_spec.spl` | `:103` `process_run_timeout(simple_binary, ["run", RSS_PROBE, "{corpus_count}"], 120000)` | **unknown** | an **RSS** measurement probe. Resident-set size on the tree-walk interpreter is not the product lane's RSS; the number measured is not the number claimed. |
| `test/03_system/gui/wm_compare/famous_site_corpus_spec.spl` | `:455` `process_run_timeout("bin/simple", [...])` | **unknown** | renderer **perf** corpus, ~100 pages. Same objection: timing on the interpreter is not the product lane. Carries an open perf bug row (§4). |
| `test/system/wm_compare/famous_site_corpus_spec.spl` | `:425` | **unknown** | mirror-tree duplicate of the above. |

**On "status": none of these three specs appears in `doc/08_tracking/test/test_db.sdn`
or `doc/08_tracking/test/test_result.md`** (0 matches for each basename), so
whether they currently pass could not be established statically, and no spec was
executed for this census. This matters for the word *vacuous*, which properly
means **green but blind**. A lane-shifted spec that is currently RED is a
different finding — "failing, plausibly because of the lane shift" — and
`host_gpu_lane_spec` is the likeliest candidate for that reading, since an
`it` demanding native runtime-queue evidence may well fail outright on the
interpreter. Read the four rows above as *lane-shifted and blind to the lane they
claim*; the green/red half is unestablished.

**Hand-reclassified IMMUNE (23 of the 29).** The dominant repo idiom is
deliberately multi-lane and correct: build the native leg with
`compile --native -o <ELF>` (or `native-build`) and **execute the ELF**, using
`bin/simple run <src>` only as the *declared interpreter oracle*. Those specs get
the interpret lane on the `run` leg because that is what they ask for, and the
native leg is immune per §1.4:

`controlflow_bool_codegen_regression_spec.spl` (`it "…under interpreter"` /
`it "…under native codegen"`, `:183` run + `:192` `compile --native`),
`cooperative_green_compiled_handle_array_blocker_spec.spl`,
`cooperative_green_imported_fallback_blocker_spec.spl`,
`multicore_green_blocking_compensation_gap_spec.spl`,
`multicore_green_fairness_preemption_gap_spec.spl`,
`multicore_green_parallelism_bound_gap_spec.spl`,
`multicore_green_thread_yield_gap_spec.spl`,
`native_channel_any_equality_regression_spec.spl`,
`native_function_value_loop_return_blocker_spec.spl`,
`native_function_value_loop_return_regression_spec.spl`,
`native_function_value_param_array_regression_spec.spl`,
`thread_spawn_native_zero_join_blocker_spec.spl`,
`native_backend_e2e_system_spec.spl` (×2 trees, `:82` `compile --native`; its
`:233` `run src/app/compile/native.spl` runs a *tool*, not the SUT).

Also reclassified IMMUNE because the spawned `run` produces **text**, whose
content does not depend on the engine that produced it:
`riscv_gen2_hwir_foundation_spec.spl` (11 `run src/app/cli/vhdl_compile_entry.spl`
sites emitting VHDL), `runtime_backend_boundaries_audit_spec.spl` (runs an audit
script), `portable_numeric_capabilities_spec.spl` (×2, derives lowering plans),
`rsa_modexp_montgomery_barrett_spec.spl` (`:60` passes `--mode=interpreter`
explicitly), `linkers_log_modes_spec.spl` (×2) and `ui_chromium_log_modes_spec.spl`
(×2) (CLI help / log-mode text).

**UNCLEAR — needs a human read (2 of the 29):**

- `test/01_unit/app/ui/browser_backend_runtime_queue_spec.spl:54` —
  `rt_process_run(simple_binary(), ["run", probe])`, `it "surfaces queue evidence
  on GPU frames and resets it on cached frames"`. Whether the queue evidence is
  engine-dependent was not established.
- `test/01_unit/app/llm_caret/messaging/database_execution_spec.spl:64,77` —
  `it "uses a cached native executable even for an interpreter-hosted caller"`.
  The spec is explicitly about a native/interpreter boundary; which side the
  spawn is meant to be on was not established.

**UNCLEAR — heuristic-negative (341).** These are lane-shifted but the heuristic
found no native/JIT intent. They are *not* immune — they run their child on the
interpreter when the product default is JIT — but they are not evidence for a
codegen bug either. The single largest homogeneous sub-bucket is **209
`*_log_modes_spec.spl` files** (104 under `test/02_integration/app`, 105 under the
`test/integration/app` mirror), which assert CLI help text and log-mode output;
those are very likely benign. They are listed in
`build/vsc/census/unclear_lane_v3.txt` rather than being asserted clean.

**UNCLEAR — subcommand not determinable (126).** Sampled cases include
`shell("cd {root} && … {simple_bin} run {bug_add_main} --id=…")` (a real `run`
whose subcommand is not adjacent to a literal), and
`cli_native_build_main_contract_spec.spl`, which is a *source-text* assertion
(`expect(source).to_contain("process_spawn_async(simple_bin, shard_args)")`) and
spawns nothing at all. Both shapes are in this bucket; it needs a per-file read.

---

## 4. Bug-DB cross-reference — false closures

`doc/08_tracking/bug/bug_db.sdn` carries **1,336 rows** in the `bugs` /
`bugs_active` tables — every one with `valid=true`; statuses are 1,270 `open`,
50 `fixed`, 15 `fix-implemented-verification-pending`, 1 `resolved-duplicate`.
(The brief cited 1,092 actionable rows on this host. That figure was **not
reconciled** with the 1,336 counted here — a different filter, a different
snapshot, or a different table selection would all explain it, and none was
verified. The cross-reference below is against all 1,336.)

**422 rows name a `test/…_spec.spl` path** (429 bug↔spec pairs, 406 distinct
specs, of which 386 exist on disk). Statuses of those 422: 397 `open`, 20
`fixed`, 5 `fix-implemented-verification-pending`.

Only **26** of the 406 bug-named specs are in the 572 shell-out population at all.

| question | answer |
|---|---|
| bug_db rows naming one of the **4 hand-verified VACUOUS** paths | **1** — `open` |
| bug_db rows naming **any** LANE_SHIFTED_RUN spec | **17** — **all 17 `open`** |
| bug_db rows with status `fixed` / `fix-implemented-*` naming a lane-shifted spec | **0** |

**There is no false closure in `bug_db.sdn` attributable to a vacuous spec.**
That is the measured result, and it is a genuine negative — not an unchecked one.
The 17 rows are listed in `build/vsc/census/bugs_on_shifted_v3.tsv`. The one that
touches a hand-verified VACUOUS spec:

- `simple_web_layout_corpus_perf_2026-05-31` (P3, **open**) → repro
  `test/03_system/gui/wm_compare/famous_site_corpus_spec.spl`. This is an
  **unverifiable repro**, not a false closure: a perf bug whose repro measures
  the interpreter.

By contrast, and *not* one of the 17:
`jit_array_element_i64_storage_truncation_2026-08-17` (P1, **open**) → repro
`test/03_system/compiler/i64_interpolation_engine_parity_spec.spl`. That spec is
**IMMUNE_EXPLICIT_LANE** — it declares its engines, which is exactly why it falls
outside the lane-shifted set. It is the model the fix should copy.

### 4.1 The prose bug records

`doc/08_tracking/bug/` holds **3,999 `.md` files**. 93 of them mention a
lane-shifted spec by basename (1,395 mentions). Filtering for a
FIXED / RESOLVED / CLOSED status line leaves **13 rows across 8 distinct
documents** — these are **false-closure *candidates*, not confirmed false
closures**: "the document names the spec" is weaker than "the spec is the
evidence", and each needs a human read of the closure argument.

| bug document | status line | lane-shifted spec named | this census's verdict on that spec |
|---|---|---|---|
| `simple_web_renderer_ttf_glyph_metrics.md` | `Status: Resolved` | `famous_site_corpus_spec.spl` (both trees) | **VACUOUS** — strongest candidate |
| `riscv_gen2_system_spec_truncated_2026-08-12.md` | `Status: resolved` | `riscv_gen2_hwir_foundation_spec.spl` | reclassified IMMUNE (text output) |
| `app_interpreter_deletion_evidence_package_2026-08-11.md` | `Status: FIXED` | `runtime_error_stack_spec.spl` | lane-shifted, heuristic-negative |
| `test_runner_unanchored_skip_substring_2026-08-21.md` | `Status: FIXED` | `check_skip_log_modes_spec.spl` (both trees) | log_modes bucket, likely benign |
| `parser_comparison_chain_misread_as_generic_args_2026-08-18.md` | `Status: FIXED` | `cli_log_modes_spec.spl` (both trees) | log_modes bucket, likely benign |
| `test_tree_divergence_sample4_15_triage_2026-08-08.md` | `FIXED` | `app_mcp_intensive_spec.spl` (both trees) | lane-shifted, heuristic-negative |
| `test_tree_divergence_sample6_15_triage_2026-08-09.md` | `FIXED` | `app_mcp_intensive_spec.spl` (both trees) | lane-shifted, heuristic-negative |
| `app_root_run_path_passed_as_option_2026-06-12.md` | `Status: resolved` | `dynsmf_autoload_policy_spec.spl` | lane-shifted, heuristic-negative |

**One name to act on:** `simple_web_renderer_ttf_glyph_metrics.md`, marked
`Status: Resolved`, whose named spec is a hand-verified VACUOUS perf corpus.

---

## 5. Side findings (observed, not chased)

- **An `.smf` produced by `compile` bus-errors when executed by this seed.**
  `bin/simple compile build/vsc/child2.spl -o build/vsc/child2.smf` succeeds, then
  `bin/simple build/vsc/child2.smf` prints `Bus error` and no program output —
  from a clean shell **and** with `SIMPLE_EXECUTION_MODE=interpret`, on a
  three-line hello-world. This blocked the attempt to determine whether the SMF
  execution path is lane-sensitive, so that question stays open. Three specs in
  the AOT-immune class run an SMF leg
  (`cooperative_green_compiled_handle_array_blocker_spec.spl:105`,
  `cooperative_green_imported_fallback_blocker_spec.spl:98`,
  `thread_spawn_native_zero_join_blocker_spec.spl:135`, all
  `shell("timeout 20s " + SIMPLE_BIN + " " + SMF_PATH)`). Whether *their* SMFs
  bus-error was not tested and no claim is made about them. Worth a bug row:
  observed on a fixture, aarch64, seed at 50,093,192 bytes.
- **`native-build` is unexercisable on this host.** Both lanes gave
  `native-build worker exited with code 1` on a hello-world; the 20 `native-build`
  sites are classified by analogy with `compile --native`, not by direct test.
- **`skip_if_interpreter` is a near-empty vector, not a second problem.**
  `is_interpreter_mode()` / `skip_if_interpreter` (`src/lib/nogc_sync_mut/spec.spl:184-207`)
  would *always* skip under the runner. Exactly **1** spec file under `test/`
  references either. Noted and closed.

---

## 6. Proposed mechanical fix (NOT applied)

### 6.1 There is no existing spawn helper that scrubs

Checked, and named so the gap is not re-litigated:

- **`src/lib/nogc_sync_mut/io/process_ops.spl`** — the canonical spawn surface.
  `process_run(cmd, args)`, `process_run_bounded(cmd, args, timeout_ms, max_output_bytes)`,
  `process_spawn_piped(cmd, args)`, `process_run_timeout_unix/windows(cmd, args, timeout_ms)`.
  **No variant accepts an environment.** There is no place to put a scrub, which
  is the structural reason 1,028 of 1,050 sites don't have one.
- **`src/lib/nogc_sync_mut/spec/engine_probe.spl:132-146`** — sets both variables,
  runs, restores. It is an **in-process** toggle for the current process, not a
  spawn helper, and it cannot help a child that is already spawning.
- **`src/compiler_rust/lib/std/src/spec/mode_runner.spl:121,258`** — `ModeRunner`
  *panics* rather than switching in-process, with the message "Run one process per
  mode with `SIMPLE_EXECUTION_MODE` instead." It states the requirement and
  provides no mechanism to meet it.

So the repo has a documented rule, one in-process toggle, and no spawn-side
implementation. The two idioms that work today (`env -u …` in the arg list, and
`"SIMPLE_EXECUTION_MODE=" + mode` concatenation) are hand-rolled per spec.

### 6.2 The proposal

Add one helper beside the existing spawn primitives — `process_ops.spl`, or a
`std.spec` sibling so it is obviously test-facing:

```
pub fn process_run_lane(engine: text, cmd: text, args: [text]) -> (text, text, i64)
```

- `engine` is **required, with no default**. Choosing a lane becomes an explicit,
  reviewable act; there is no way to spawn "whatever was inherited".
- Accepts exactly the values `parse_str_checked` accepts (`jit`, `interpret`,
  `interpreter`, `interpret-optimized`, `cranelift`, `llvm`, `wasm`, …) plus
  `inherit` for the rare spec that genuinely wants the parent's lane — spelled
  out, so it reads as a decision.
- Implementation is the shape already proven in `mem_cli_spec.spl` and by the
  §1.2 fixture: prepend
  `env -u SIMPLE_EXECUTION_MODE -u SIMPLE_RUNTIME_MODE SIMPLE_EXECUTION_MODE=<engine>`
  (omit the trailing assignment for the JIT default, since unset ⇒ JIT).
  `-u` first is load-bearing — assignment alone leaves the stale
  `SIMPLE_RUNTIME_MODE` behind for the `.spl`-level readers in
  `spec.spl` / `font_registry.spl`.
- Sibling wrappers for the other primitives actually used by specs:
  `process_run_timeout_lane`, `process_spawn_async_lane`.

Migration, in the order that buys the most per edit:

1. The **4 hand-verified VACUOUS paths** — these are wrong today. `host_gpu_lane_spec.spl`
   additionally needs its `--mode=native` argument reconsidered, since §1.5 shows
   the seed does not accept it as a lane selector at all; the flag is currently
   inert.
2. The **2 UNCLEAR native-intent specs**, after a read.
3. The **126 UNCLEAR_UNKNOWN_SUBCMD** files, which need a read to be classified.
4. The remaining **341** heuristic-negative lane-shifted specs — mechanical, and
   the 209 `*_log_modes_spec.spl` files are one repetitive edit.

Then, and only then, a ratchet is meaningful: a `scripts/check/` guard that counts
unscrubbed `run` spawns in `*_spec.spl` and fails on an increase, baselined at
whatever the count is when step 1-2 land. Filing it before the population is
understood would just freeze 370 files.

**Not proposed: changing what the runner exports.** `test_runner_execute.spl:209-212`
needs the spec process interpreted for the BDD intrinsics. The fix belongs at the
spawn boundary, not at the runner.

---

## 7. Artifacts

All under `build/vsc/census/` (gitignored, regenerable):

| file | contents |
|---|---|
| `sites_v3.tsv` | 1,050 spawn sites: file, line, subcommand, lane-declared, aot |
| `per_file_v3.tsv` | 572 files with class |
| `lane_shifted_v3.txt` | the 370 |
| `vacuous_v3.txt` | the 29 native-intent candidates before hand review |
| `unclear_lane_v3.txt` | the 341 |
| `handcheck.txt` | spawn lines + `it` names for all 29, the hand-review input |
| `bug_spec_rows.tsv` | 429 bug↔spec pairs from `bug_db.sdn` |
| `bugs_on_shifted_v3.tsv` | the 17 bug rows on lane-shifted specs |
| `vacuous_hand.txt` | the 4 hand-verified VACUOUS paths |
| `md_false_closures.tsv` | the 13 rows / 8 documents of §4.1 |
| `site4.awk`, `run_v3.sh`, `probe_*.sh`, `cmp_offsets.sh` | the scripts, rerunnable |

Fixtures: `build/vsc/child.spl` (prints the two variables),
`build/vsc/child2.spl` (the `rt_signal_install` engine oracle),
`build/vsc/lane_inherit_spec.spl`, `build/vsc/lane_scrub_spec.spl`.
