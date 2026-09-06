# Lane guide — unified 2D event/panel/offload campaign

Read `unified_2d_event_panel_offload_2026-07-30.md` (same dir) for decisions D1–D9
and the lane table. This file is the operating manual every lane agent follows.

## Hard rules (violating any = the change is rejected)

- Pure Simple only: `.spl` / `.shs`. No Python, no Bash scripts, no new C/Rust.
- NO inheritance. Composition / traits / mixins only.
- Generics use `<>` not `[]`.
- **D8 — new 2D event/panel code lives ONLY in `src/lib/common/`.** No tier
  mirrors (`gc_async_mut`, `nogc_*`, ...). If you touch a drifted tier copy,
  consolidate or delete it in the same change.
- NEVER skip a failing test without approval. NEVER convert TODO to NOTE.
- Do NOT over-engineer. Shortest diff that works and is proven.
- Do NOT commit. Do NOT `git add`. Leave changes in the working copy.
- Work on `main`; never create a branch.

## Test rules (SSpec)

- Spec path mirrors source: `src/lib/common/ui/x.spl` →
  `test/01_unit/lib/common/ui/x_spec.spl`.
- Use `assert_true` / `assert_false` / `assert_eq`. `to_be_true` / `to_be_false`
  are REJECTED by the runner.
- Run: `bin/simple test test/01_unit/.../x_spec.spl > /tmp/x.log 2>&1` then grep
  the LOG FILE. Piping the runner breaks `$?` and truncates output.
- **Only the `Results:` line is authoritative.** Per-example ticks lie.
- Lint before claiming done: `bin/simple lint <file>`. Note: lint does NOT catch
  syntax errors — a green lint on a non-parsing file is meaningless, so the spec
  actually running is the real gate.

## Known landmines (do not rediscover these)

- `list.get(i)` returns a tag-boxed word (value<<3) under JIT. Use `xs[i]`.
- Native `Dict.get` miss returns 0/false/NULL, not nil — `?? default` is unsafe.
- `?? ` on a raw i64 corrupts the value 3 (nil sentinel IS 3).
- `char_code_at` is O(i) → any scan over it is O(N²).
- Bounds convention is HALF-OPEN everywhere: left/top inclusive, right/bottom
  exclusive. `HitProxy2D.create(node_id, left, top, right, bottom)` takes
  ABSOLUTE edges, not x/y/w/h.
- `to_text` on an erased `Any` bool is corrupt; compare `== true` instead.

## Existing green foundation — build on it, don't re-invent

| File | State |
|---|---|
| `src/lib/common/engine/interaction/{pointer_event,event_route,hit_proxy,hit_test,pointer_capture}.spl` | 15/15 green |
| `src/lib/common/engine/interaction/draw_ir_hit_bridge.spl` | 10/10 green — DrawIR → `DrawIrHitForest{proxies,parents,node_names}` |
| `src/lib/common/engine/interaction/window_event_adapter.spl` | 9/9 green — `WindowEventRecord` → `PointerEvent2D` |
| `src/lib/common/ui/panel2d.spl` | written, UNVERIFIED (no spec yet) |

## Working-copy hazard — READ THIS, it has bitten twice

An out-of-band `jj workspace update-stale` from a parallel session has TWICE
deleted uncommitted files in this shared working copy — sources, specs, and a
plan doc — with **no error and a clean-looking git status**.

- **A missing `Results:` line can mean the spec FILE IS GONE, not that it failed.**
  The runner prints `error: test file not found`. Never read silence as green,
  and never read it as red either — check the file exists first.
- **Recovery:** `jj --ignore-working-copy op log --no-graph -n 25`, then probe
  ops with `jj --ignore-working-copy --at-op=<op> file show <path> | wc -c` until
  you find one with a non-zero size, then redirect that to the path.
- **Insurance is mandatory:** every file you author or edit, copy immediately to
  `/tmp/claude-1000/-home-ormastes-dev-pub-simple/243d611f-3f40-4b9b-ab73-cf4b57ac4e66/scratchpad/lane_backup/<same relative path>`
  (`install -D <file> <backup>/<file>`). Re-verify your files exist on disk right
  before you report.

## Do not stall on background monitors

A monitor/background task will NOT reliably notify you. Do not sit in a wait
loop — one lane burned 37 tool calls waiting. Run with a hard
`timeout 600 <cmd> > /tmp/<name>.log 2>&1`, then grep the log file. If there is
still no `Results:` line, that IS your answer: report it as a hang with evidence.

## Cross-tier alias trap (cost L4 a wrong-looking failure)

The unprefixed import alias `std.gpu.engine2d.<mod>` resolves to the
**nogc_async_mut** copy, not `gc_async_mut`. A fix applied only to the gc copy
silently does nothing. If you change behaviour behind such an alias, check which
tier copy the specs actually load before concluding your change is broken.

## Reporting back

Return only: files changed, the exact `Results:` lines you observed, and any
blocker. No prose summaries of the code. If a pre-existing failure blocks you,
verify it also fails at HEAD before reporting it as pre-existing.
