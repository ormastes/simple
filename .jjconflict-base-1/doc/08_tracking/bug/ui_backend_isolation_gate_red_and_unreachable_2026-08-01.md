# UI backend-isolation gate: red since 2026-07-25, and never executed in CI

- **Date:** 2026-08-01
- **Guard:** `scripts/check/check-ui-backend-isolation.shs`
- **Baseline:** `scripts/check/ui_backend_isolation_baseline.txt`
- **Measured at:** `2aacc58837ae3c77f7b601e0000785e9e59c5a94` (origin/main tip)
- **Related:** `doc/08_tracking/bug/check_script_wiring_orphans_2026-08-01.md`
  (the guard-wiring audit that surfaced this red), and
  `doc/08_tracking/bug/ci_gate_enforcement_surface_2026-07-07.md`
  (which recorded this gate as "GREEN after absorb / CI-enforced" — both halves
  of that claim were already false by 2026-07-25, see §2).

## 1. Summary

This guard is *not* one of the 364 orphaned guards. It is wired into the
`code-idiom-gates` job of `.github/workflows/repo-hygiene.yml`, its step is a
plain `run:` with no `continue-on-error`, so a non-zero exit **does** fail the
step and the job. By that reading it is gating.

It nevertheless enforced nothing, for two independent reasons:

1. **It never ran.** It is step 5 of the job. Step 4
   (`check-cpu-hotloop-idiom.shs`) fails on every push to `main`, and GitHub
   Actions aborts the remaining steps. Steps 5–9 report `skipped`. The UI gate,
   the TUI closure gate, the workspace root guard, the guard-wiring ratchet and
   the extern report had **not executed once**.
2. **Nothing was gated on the result anyway.** `main` has **no branch
   protection** (`GET /repos/ormastes/simple/branches/main/protection` → 404
   "Branch not protected"). Pushes land regardless of workflow conclusion.

So the failure mode is a third variant of "wired in name only": wired, gating in
principle, unreachable in practice, and non-blocking even if reached.

The workflow already carried a comment explaining that `repo-hygiene` was split
into its own job precisely so a red step would not "mask their per-gate
pass/fail signal" — and then five gates were placed in one sequential job,
reproducing the same bug one step further down.

## 2. The gate has been red since at least 2026-07-25

Replaying the guard's own set logic against `37cda4befdc` (2026-07-25) gives
`current=556`, `baseline=563`, **`new=23`**, `stale=30`. The baseline has been
byte-stable at 563 entries since that commit. So the gate would have exited 1
then too. It was reported GREEN because it was never run.

The 31 findings at HEAD are therefore **not 31 new breaches**. 23 of them
already matched on 2026-07-25; 2 more gained real `rt_*` use since; 6 are files
that did not exist then. The `--diff-filter=A` date on all 31 is `7f5a55fa46e`
(2026-08-01) only because that commit is the ~109.5k-file restore after the
second ENOSPC truncated-tree wipe; it says nothing about file age.

## 3. Rule defect: bare-token matching (7 of 31 findings were false positives)

The RT rule was `\brt_[a-z0-9_]+` — a bare token, anywhere in a `.spl` file,
with no distinction between code, comments, docstrings, strings, or unrelated
identifiers. Observed mis-scored cases, each re-read by hand:

| File | What actually matched | Verdict |
|---|---|---|
| `src/app/ide/draw_sdd_sanity.spl` | `val rt_nodes = again.nodes.len()`, `val rt_edges = ...` — **local variables**, no extern, no FFI | false positive |
| `examples/06_io/ui/wm_widget_showcase_gui.spl` | only lines 12 & 14, both `#` comments, whose text states the module does **not** register `rt_winit_*` | false positive — flagged for documenting its own compliance |
| `src/lib/common/ui/draw_ir_v3_backend_enums.spl` | only line 45, a `#` comment header | false positive |
| `src/app/devhub/retry.spl` | a comment saying it calls `std.nogc_sync_mut.sffi.system.sleep_secs` **instead of** `rt_sleep_secs` | false positive — the compliant path |
| `src/app/devhub/cmd_minio.spl` | `rt_http_request` inside a user-facing `print_error("...")` string | false positive |
| `src/app/devhub/cmd_storage.spl` | prose in a docstring | false positive |
| `src/app/cli/_CliMain/main_and_help.spl` | a `#` comment about a crash in `rt_env_set` | false positive |

### Fix applied

The RT rule now requires the token to be **used as code** — an
`extern fn rt_*` declaration or an `rt_*(` call — and each candidate line is
re-checked after its `#`-comment tail is stripped (quote-aware, so a `#` inside
a double-quoted string does not start a comment). `BACKEND_PATTERN` gained the
same comment filter and tolerates whitespace before `(`.

This makes the gate **stricter per finding, not weaker**: it still fires on
every `extern fn rt_*` and every `rt_*(` call site. Repo-wide it removes 63
prose-only files (`current` 545 → 482) and **zero** real declarations or calls
— every eliminated file was read to confirm it contained prose only.

## 4. Baseline: 105 stale entries removed, 0 added

The `--update-baseline` path was **not** used (it would have absorbed the live
violations). The new baseline is `old ∩ current`, computed by deleting only
non-reproducing lines and preserving all `#` provenance annotations.

- 563 → **458** entries; 105 removed.
- Of those 105: **22** files were deleted from the tree; **83** still exist but
  no longer match (prose-only under the corrected rule, or genuinely migrated).
- **Nothing was added.** Verified: `grep -cxFf new24.txt kept.txt` = 0.

## 5. Remaining 24 genuine violations — per-file disposition

All 24 are real `extern fn rt_*` declarations and/or `rt_*(` calls in app,
example, or UI-lib code. All are **pre-existing debt the baseline never
captured**, not regressions introduced by this change. They are deliberately
left unbaselined; the gate stays red on them.

### G1 — Baremetal / firmware entry points (3) — OWNER DECISION NEEDED, not app debt
`examples/09_embedded/simple_os/arch/riscv64/serial_shell_entry.spl`,
`examples/09_embedded/simple_os/arch/x86_64/char_code_at_loop_probe_entry.spl`,
`examples/09_embedded/simpleos_nvme_fw/fw_rv32/entry_smp.spl`
(`rt_rv32_*`, `rt_riscv_uart_put`, `rt_port_outb`, `rt_baked_fs_*`).

These are kernel/firmware entry code. The baseline's own 2026-07-07 annotation
absorbed ~50 sibling `arch/*_entry.spl` files with the rationale that "`rt_*`
here is legitimate direct hardware/runtime access at the kernel/baremetal layer
… not an app-layer rendering-facade bypass". By the architecture layer table
these files are the *Runtime/Backend-impl* layer, which **may** declare `rt_*`;
they only appear here because `examples/**` is a scan root.

The consistent fix is a **scan-root exclusion** for baremetal firmware paths
(the allowlist already carves out `src/app/interpreter/ffi/**` and
`src/lib/nogc_sync_mut/ui/**` for exactly this reason) — *not* 3 more baseline
lines. That is a scope change with an owner and is deliberately **not** made
here. Until it is, these 3 hold the gate red.

### G2 — `devhub` tool, non-rendering runtime FFI (6)
`adapter_minio.spl` (`rt_http_request/_bytes`, `rt_http_download/_upload/_put_file`, `rt_time_now*`),
`cmd_api.spl`, `cmd_wiki.spl`, `main.spl` (`rt_cli_get_args`),
`output.spl` (`rt_process_run_inherit`), `wiki_git.spl` (`rt_file_*`).

### G3 — CLI / build / IO tooling (5)
`src/app/check/targets.spl` (`rt_dir_exists`),
`src/app/cli/cli_helpers.spl` (`rt_path_absolute`),
`src/app/cli/native_build_worker.spl` (`rt_exit`),
`src/app/cli/vhdl_compile_entry.spl` (`rt_cli_get_args`, `rt_env_set`),
`src/app/io/source_discovery.spl` (`rt_dir_walk`, `rt_path_absolute`).

### G4 — portal / web server (4)
`src/app/portal/git_repo.spl`, `src/app/portal/server.spl`,
`src/app/portal/template.spl`, `src/app/web_dashboard/server.spl`
(`rt_file_exists`, `rt_file_read_text`, `rt_env_get`).

### G5 — misc app (4)
`src/app/llm_caret/main.spl` (`rt_bytes_to_text`),
`src/app/memstat/main.spl` (`rt_mem_attr_*`),
`src/app/mem/top_tui.spl` (`rt_term_poll`, `rt_term_read_timeout`),
`src/app/test/font_evidence_runner.spl` (`rt_bdd_*`, `rt_string_bytes`).

### G6 — UI library (1) — highest priority, most on-point for this gate
`src/lib/common/ui/native_scalar_text.spl` — declares and calls
`rt_raw_i64_to_string`. This is a UI lib under `src/lib/*/ui`, the exact layer
the architecture forbids from declaring `rt_*`.

### G7 — UI example (1)
`examples/06_io/ui/wm_full_stack_demo.spl` — `extern fn rt_sleep_ms` + call at
line 481, inside a UI example.

## 6. Cost of full compliance

Every extern family involved already has a canonical stdlib home:
`src/lib/nogc_sync_mut/ffi/io.spl` (`rt_path_absolute`, `rt_dir_walk`),
`ffi/system.spl` (`rt_env_set`, `rt_sleep_ms`), `io/http_sffi.spl`
(`rt_http_request`), `fs.spl`, `conf.spl`. So the remediation is mechanical per
file: delete the local `extern fn rt_*` re-declaration, `use` the stdlib module,
call the wrapper.

Prioritised order: **G6 → G7** (in-scope UI layer, 2 files, ~1 h);
**G1** (owner decision on scan-root scope, 0 code changes);
**G3 → G4 → G5 → G2** (18 files of ordinary FFI-facade migration).

Estimated cost for G2–G7 (21 files): roughly 1–2 days including per-app smoke
runs. It is **not** a pure text substitution — `adapter_minio.spl` alone routes
seven HTTP externs and is the MinIO data path, so it needs real exercise, and
these apps are not covered by a spec that would catch a mis-wired extern (an
unregistered `@extern` returns nil/0 silently rather than failing to link).

Caveat worth recording: the stdlib itself re-declares several of these externs
in multiple modules (`rt_env_get` appears in both `src/lib/log.spl` and
`src/lib/nogc_sync_mut/coverage.spl`), so "one canonical facade per extern" is
not yet true even inside `src/lib`. Migrating apps onto facades should not
silently multiply those re-declarations.

## 7. Non-vacuity evidence (observed, not inferred)

Against the fixed guard and shrunk baseline, sabotaging a real clean source file
(`src/app/jj/sync.spl`) and re-running:

| Sabotage | Expected | Observed |
|---|---|---|
| none (control) | 24 new, victim absent | `new=24`, victim absent |
| `# comment mentioning rt_evil_hook` | not flagged | `new=24`, victim absent |
| `rt_evil_hook(1)` call, no decl | flagged | `new=25`, `…new_violation=RT:src/app/jj/sync.spl` |
| `extern fn rt_evil_hook(x: i64) -> i64` | flagged | `new=25`, `…new_violation=RT:src/app/jj/sync.spl` |
| `val b = MetalBackend(1, 2)` | flagged | `…new_violation=BACKEND:src/app/jj/sync.spl` |
| restored | back to control | `new=24`, victim absent |

The `MetalBackend(` case also proves the BACKEND half is live rather than
vacuous — it has **0** entries in the baseline and had never fired.

## 8. Status

- Guard rule: **fixed** (stricter, 7 false positives eliminated).
- Baseline: **458**, 105 stale removed, 0 added, `…_baseline_stale` count now 0.
- CI masking: **fixed** — all six gate steps carry `if: ${{ !cancelled() }}`, so
  each reports its own verdict. The job still fails if any gate fails.
- Gate result at HEAD: **`ui_backend_isolation_new=24`, exit 1 — still RED**, by
  design, on genuine pre-existing debt.
- **`main` remains unprotected**, so no workflow conclusion blocks any push.
  Making this job a required check is a separate, owner-level action.

## 9. Pre-commit hook: still blocked

The tracked pre-commit hook **cannot** be installed yet. This guard exits 1 on a
clean checkout of `main`, so installing the hook would fail every commit in the
repo — which is exactly why a sibling session declined to auto-install it.

Unblock requires the gate to reach `new=0`. Cheapest credible path: resolve
**G1** by scan-root scope decision (3 files, no code change), then migrate
**G6/G7** (2 files), then G2–G5 (18 files). Only after `new=0` should the hook be
installed, and it should be installed as a **symlink**, not a copy — the
guard-wiring ratchet fails copied hooks because they go stale silently.
