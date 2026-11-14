# `cs` caret dashboard grows ~0.6-5 GB/h under the seed JIT lane (JIT never frees)

- **Date:** 2026-11-14
- **Severity:** P1 (two live `cs` sessions reached 17.7 GB and 13.0 GB RSS after 22 h,
  starved the host, and made a bootstrap Stage 2 fail its RSS cap)
- **Status:** open. Root cause attributed. Operational mitigation verified. Seed fix not attempted.
- **Owner layer:** Rust seed codegen. Measured on the Cranelift JIT lane; LLVM `emit_drop` (`llvm/emitter.rs`) is also a no-op, so ahead-of-time native builds probably leak the same way (not measured). Not `src/app/llm_caret`.
- **Related:** `seed_jit_array_copy_never_freed_2026-10-19.md` (same mechanism, array-copy case),
  `doc/01_research/compiler/memory_model/engine_memory_model_study_2026-11-14.md` P14
  (records the same live processes but does not attribute them; this record attributes them).

## Symptom

`<seed> run src/app/llm_caret/cs_main.spl caret-p3` and `... caret-ctr` were started on
2026-11-13 with seed `seedhead` (sha256 `55a6b4d18e17c117…38ccbb05`, built Nov 13 19:04).
After 22 h they held 17.7 GB and 13.0 GB RSS. They were still growing at about 0.65 GB/h
(17.70 → 18.08 GB in about 35 min). RSS equals the peak, so nothing is ever returned.

## Root cause

The memory is allocated by the JIT lane, which never frees it. `cs_run_live` itself
does not accumulate.

- `MirInst::Drop` is a no-op for every type
  (`src/compiler_rust/compiler/src/codegen/instr/mod.rs`, the `MirInst::Drop` arm).
  The only free that lowering emits is for one narrow case: `rt_array_free` of the old
  value when a uniquely owned struct array field is reassigned
  (`mir/lower/lowering_stmt.rs`, the 2026-10-19 fix). Text, other array and struct
  temporaries are never freed. So every temporary
  a JIT-compiled tick allocates is kept forever. That includes the clock text, frame
  rows, `chars()` arrays, captured screen rows and the per-2 s roster rebuild.
- On the Nov 6 seed (`seed-try-target`, sha256 `87693d9e927f9bd5…c78284aa7`),
  `cs_main.spl` fails HIR lowering
  (`cannot infer field type while lowering PureDatabase._do_select_bitmap_owned_v1`).
  The whole module drops to the interpreter, and memory stays flat.
- On `seedhead` the module is admitted to hybrid JIT (`reason=hybrid-interp-splice`
  for only a list of `rt_*` externs). So the old no-free gap now applies to a 22-hour
  loop. It is inferred, not measured, that no new leak was introduced: the Nov 6 seed
  never ran this module on the JIT, so there is no same-lane comparison.
- App code was checked and is bounded. Every per-tick value in `cs_run_live` (`prev`,
  `d`, `last_clock`, the frame) is replaced each tick, and smux VT history is capped at
  2000 rows (`vt_screen.spl` `history_limit`). Captures are bounded too. The only
  list that grows without limit is `CsDashboard.log`. It gets one entry per operator
  command or launch, so it grows with commands, not with time, and cannot cause
  idle growth.

## Evidence (same source: origin/release/1.0.0 `fc3ffeeccf9`)

Each run was live mode inside an isolated tmux server, under
`systemd-run --user --scope -p MemoryMax=4G timeout --foreground`, with VmRSS sampled
every 30 s. `--foreground` is required. Without it `timeout` puts the seed in a
background process group and the dashboard stops on SIGTTOU.

| seed / engine | scenario | duration | VmRSS |
|---|---|---|---|
| seedhead, default (hybrid JIT) | idle, 0 agents | 10 min | 596.7 → 660.8 MB over the last 6.5 min (+4.9 MB/30 s ≈ 0.6 GB/h, the live rate) |
| seedhead, default (hybrid JIT) | 1 quiet Claude Code pane | 8.5 min | 683.5 → 1449.4 MB (+45 MB/30 s ≈ 5.4 GB/h) |
| seedhead, default (hybrid JIT) | + `opencode` shim flooding 20 lines/s | 2 min | 1593 → 1818 MB (+56 MB/30 s) |
| seedhead, `SIMPLE_EXECUTION_MODE=interpreter` | idle, 0 agents | 5 min | 390.6 → 383.8 MB (flat) |
| seedhead, `SIMPLE_EXECUTION_MODE=interpreter` | 1 Claude Code pane | 3 min | 346.6 → 346.6 MB (flat) |
| Nov 6 seed (whole-module interpreter) | idle, 0 agents | 7 min | 467.6 → 465.3 MB |
| Nov 6 seed (whole-module interpreter) | 1 quiet Claude Code pane | 6 min | 405.8 → 400.3 MB |
| Nov 6 seed (whole-module interpreter) | line flood 20 lines/s, past the 2000-row cap | 7 min | 358.9 → 358.4 MB |
| Nov 6 seed (whole-module interpreter) | full-screen SGR redraw 10 fps, 2 agents | 3.5 min | 357.5 → 341.0 MB |

On the interpreter the dashboard stayed functional: the clock advanced, `/launch claude`
worked, and the roster and screen updated.

### Minimal repro (same binary, two engines)

```
use app.io.mod.{file_read}

fn rss_kb() -> text:
    for line in file_read("/proc/self/status").split("\n"):
        if line.starts_with("VmRSS:"):
            return line.replace("VmRSS:", "").trim()
    "?"

fn main() -> i64:
    print "start rss " + rss_kb()
    var keep = ""
    var i = 0
    while i < 200000:
        keep = "x" + i.to_text()
        i = i + 1
    print "end rss " + rss_kb() + " " + keep
    0
```

| `SIMPLE_EXECUTION_MODE` (seedhead) | start | end | per iteration |
|---|---|---|---|
| `jit` | 143.4 MB | 181.8 MB | ~197 B kept per iteration |
| `interpreter` | 113.9 MB | 114.1 MB | ~1 B |

## Mitigation (verified)

Run long-lived `cs` sessions with `SIMPLE_EXECUTION_MODE=interpreter`. That is flat
on the same binary and source. A 50 ms-tick dashboard has no throughput need for the JIT. The
two live sessions can only be reclaimed by restarting them. Their owner should restart
them with this variable set.

## Fix (not attempted here)

The real fix is deallocation on the JIT lane: ownership or refcount release in codegen
for text, array and struct temporaries. That is a design item, not a local patch. The
2026-10-19 record already reverted one broader attempt that made things worse; only
its narrow field-store free remains live. Until it
lands, every long-running program that is admitted to the JIT has the same linear
growth, proportional to its allocation rate.

## Side findings (not fixed here)

- `bin/cs` exports `CARET_ENTRY=src/app/llm_caret/cs_main.spl`, but the source
  fallback in `bin/caret` ignores it and always runs `src/app/llm_caret/main.spl`.
- `CsDashboard.log` has no limit (it grows per command). It is not the cause above.
