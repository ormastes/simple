# M8 Design: `simple mem` CLI Data Channel (2026-07-29)

Source: `doc/02_requirements/runtime/memory_analysis/feature_simple_mem_cli.md`.
Reuses: `src/app/memstat/main.spl` (sampler), `rt_mem_attr_report` /
`rt_heap_live_bytes_by_owner` / `rt_heap_top_owners` (`src/compiler_rust/compiler/src/interpreter_extern/memory.rs`).

## 1. Subcommand wiring plan

Dispatch follows the existing flat pattern in
`src/app/cli/_CliMain/main_and_help.spl` (`elif str_eq(first, "<name>"):` ->
`cli_run_file(...)`, e.g. lines 400-459; `leak-check` at line 440 shows the
non-file-run variant calling a Simple fn directly). Add one arm:

```
elif str_eq(first, "mem"):
    return cli_run_file("src/app/mem/main.spl", _cli_args_from(filtered_args, 1), flags.gc_log, flags.gc_off)
```

New `src/app/mem/main.spl` becomes the sub-dispatcher (mirrors `src/app/os/`,
`src/app/t32/` pattern of a second-level `str_eq` switch), sub-file per verb:

| sub | file | behavior |
|---|---|---|
| `sample` | `src/app/mem/sample_entry.spl` | thin wrapper calling into `src/app/memstat/main.spl`'s existing `sample_row`/loop (rename module to `app.mem.sampler`, keep `memstat` as a compat alias per feature doc "keep the existing CSV sampler as `simple mem sample`") |
| `top` | `src/app/mem/top.spl` | live table: `--pid P` (attach via signal channel, §2) or `--profile F` (read a snapshot file, §3) |
| `snapshot` | `src/app/mem/snapshot.spl` | write one snapshot file (§3) |
| `diff` | `src/app/mem/diff_cmd.spl` | read two snapshot files, run §4 algorithm |
| `trace` | `src/app/mem/trace.spl` | spawn `prog.spl` with `SIMPLE_MEM_ATTR=1`, append periodic snapshots to a trace file |
| `gpu` | `src/app/mem/gpu.spl` | device-pool query; `--sanitize` re-exec under compute-sanitizer (out of scope for v1 wiring, stub + TODO) |
| `gate` | `src/app/mem/gate.spl` | shells `scripts/check/check-stage4-memory-gate.shs` (exists, confirmed) and relays its PASS/FAIL line |

All collectors stay off unless a subcommand needs them (`SIMPLE_MEM_ATTR`,
per `feature_backend_memory_infra_toggle.md`'s `SIMPLE_MEM_INFRA` convention)
— satisfies the zero-overhead-when-off constraint.

## 2. Live-process channel: signal dump vs MCP query

**Recommendation: signal-triggered dump to a well-known path for v1.**

Checked `src/lib/nogc_sync_mut/io/signal_handlers.spl`: it wires SIGINT/
SIGTERM/SIGHUP to a single `cleanup_handler: fn()` via `install_signal_handlers`
— **no existing SIGUSR2 hook or per-signal dispatch**. Real gap the M8 branch
must close (extend `signal_handlers.spl` with a SIGUSR2 callback, or a small
`rt_signal_register(sig, fn)` extern) before `SIMPLE_MEM_DUMP_ON=USR2` works.

Rationale over MCP: the MCP servers in `.claude/rules/code-style.md`'s table
(`simple-mcp`, `simple-lsp-mcp`, `t32-mcp`) are compiler/LSP-tool surfaces,
not embedded in arbitrary running Simple programs — wiring a live MCP
responder into every `simple run`/`simple test` target is a much bigger
surface (server loop, request routing, auth) than the acceptance bar
(`feature_simple_mem_cli.md` §Acceptance) needs, which only exercises
`trace`/`top --profile` and `diff` over files. Signal-triggered dump also
matches the file-first "bytehound model" the feature doc already commits to.
Defer MCP as a **v2** live-query channel once a shared in-process
MCP-responder library exists; v1 `top --pid P` polls the well-known dump
path after sending SIGUSR2.

## 3. Snapshot file format v1

Plain-text TSV (parseable with the same `split("\t")` / `parse_dec` style
already used in `src/app/memstat/main.spl`'s `parse_faults`), one snapshot
per file:

```
SIMPLE_MEM_SNAPSHOT_V1<TAB>{timestamp_us}<TAB>{pid}
KIND<TAB>{kind}<TAB>{live_bytes}<TAB>{peak_bytes}<TAB>{allocs}
OWNER<TAB>{owner}<TAB>{live_bytes}<TAB>{peak_bytes}<TAB>{allocs}
RSS<TAB>{rss_kb}<TAB>{pss_kb}<TAB>{pss_anon_kb}<TAB>{private_dirty_kb}<TAB>{swap_kb}
```

- Header: format tag + version (`V1`) so `diff`/`top --profile` reject
  mismatched versions instead of silently misparsing (bump on column change).
- `KIND` rows: one per `rt_heap_live_bytes_by_kind` entry (existing L3 counter).
- `OWNER` rows: one per `rt_heap_top_owners(n)` entry, gated on
  `SIMPLE_MEM_ATTR=1`; absent entirely when attribution is off — `diff`/`top`
  must handle zero `OWNER` rows.
- `RSS` row: sourced from the same `/proc/<pid>/smaps_rollup` fields
  `src/app/memstat/main.spl::sample_row` already parses — reuse
  `rollup_value`/`parse_faults` rather than re-implementing.
- TSV over CSV: kind/owner names (module paths) can contain commas, never tabs.

## 4. Diff algorithm

`simple mem diff A B`, given two parsed snapshots as `Dict<key, {live,peak,allocs}>`
keyed by `"{row_kind}:{name}"` (e.g. `"OWNER:app.foo"`, `"KIND:array"`):

1. Parse A and B independently into that dict (split on `\t`; use
   `contains_key` + index read per the native-Dict pitfalls rule — never
   `.get()` on a struct-valued dict, `.claude/rules/code-style.md`).
2. Build the union of keys from both dicts.
3. For each key: `delta_live = B[key].live - A[key].live` (missing side = `{0,0,0}`).
4. Sort rows by `delta_live` descending — "surfaces the leak top-of-list".
5. Print top N (default 20, `--all` for full): `name  A_live  B_live  delta  delta%`.
6. `--gate-kb=N`: exit non-zero when the top delta exceeds N, so `gate`/CI
   can reuse `diff` directly against a baseline.

## 5. TUI

Verified real module: `src/lib/nogc_sync_mut/tui/` (`terminal.spl`,
`style.spl`, `widget.spl`, `layout.spl`, `widgets/{text,box_widget,list,input}.spl`,
imported as `std.tui.*` per its `__init__.spl` doc comment). `top` and `diff`
render through `std.tui.widgets.list.List` inside a `std.tui.widgets.box_widget.Box`
(bordered table: name / live / peak / delta columns), driven by
`std.tui.terminal.terminal_enter_alt_screen()` for `top`'s live refresh loop.

No table-specific widget exists yet (only `List`, `Text`, `Input`, `Box`) —
v1 renders rows as fixed-width `TextWidget` lines inside a `List` rather than
waiting on a new `Table` widget.

**Plain-text fallback:** when `std.tui.terminal` reports a dumb terminal (or
stdout is not a TTY — check before calling `terminal_enter_alt_screen`), fall
back to the same TSV-derived rows printed as aligned plain lines, satisfying
"TUI works in a dumb terminal" from the acceptance section without a second
render path — the plain fallback is the TUI's row-formatting logic minus the
alt-screen/live-refresh wrapper.

## Open gaps to file as follow-up bugs
- ~~No SIGUSR2 hook in `signal_handlers.spl` (§2) — blocks `top --pid`~~ — the
  SIGUSR2 hook landed (`install_sigusr2_handler`/`on_sigusr2`), and
  `top --pid` (2026-07-30) ships as a **/proc-based poll loop**
  (`src/app/mem/live_poll.spl`) rather than the signal-dump channel, so it
  works against any pid without requiring the target to have called
  `install_mem_dump_on_usr2`. The SIGUSR2 dump+read channel still exists in
  `live_poll.spl` (`--path <file>`) as the OWNER/KIND channel for
  cooperating Simple processes, just not wired as `top --pid`'s default.
- No `Table` TUI widget — v1 workaround only (§5).
- `gpu --sanitize` re-exec, P2 sampled call-stack attribution: out of scope.
- TODO: wire `simple mem top --tui` into `src/app/mem/main.spl`'s dispatcher
  (`elif str_eq(sub, "--tui"):` in `cmd_top`, or a `--tui` flag check that
  delegates to `src/app/mem/top_tui.spl`'s render path) — the standalone
  entry (`bin/simple run src/app/mem/top_tui.spl -- --profile <file>
  [--watch N]`) and its non-TTY fallback are implemented and spec-covered
  (`test/03_system/app/mem_top_tui_spec.spl`); only the CLI wiring is
  deferred.
