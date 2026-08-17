# Jupyter kernel: `%mode`/`%%mode`/`%lanes`/`%reset`/... magics are never invoked — every cell always runs on the hardcoded local lane

- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
  and calls `dispatch_magics(SESSION_MANAGER, DEFAULT_SESSION_ID, MAGICS_STATE,
  code)` at the top of `session_execute` before any compile/execute happens,
  passing `magics.code` (stripped) and `magics.cell_mode_override` through to
  `execute_cell` exactly per "Fix direction" below. A magics-only cell (e.g.
  bare `%reset`) short-circuits to the magic's own confirmation text as the
  cell's output. Regression added:
  `test/03_system/tools/jupyter/jupyter_execution_system_spec.spl` — "wires
  %reset into execute_request" (8/8 passing on the full suite). Fixture
  routing through K4/K5/K6 via a real `%%mode` cell is now possible in
  principle (K4's `RemoteExec` still needs live QEMU tooling to prove it
  end to end; K5/K6 executors still don't exist).
- **Found:** 2026-08-07, during Stream P task P3 (E2E fixture + Docker script work)
- **Area:** `src/app/jupyter_kernel/main.spl` (P1) — magics parsing (`src/lib/nogc_sync_mut/notebook/magics.spl`, also P1) exists and is presumably spec-tested in isolation, but is dead code from the kernel's point of view
- **Severity:** high — the entire lane-selection surface (`%mode`, `%%mode`, `%lanes`, `%reset`, `%budget`, `%timeout`, `%onfault`) described in `doc/05_design/app/tools/notebook_lanes_architecture.md` §3 is unreachable from a real Jupyter session; every cell silently executes on the local `interpreter` lane regardless of what the user types

## Symptom

A cell whose first line is `%%mode interpreter(remote(baremetal(riscv32)))` (or
any other magic) does not switch lanes — it fails to execute at all, because the
magic line is fed to the compiler as literal Simple source:

```
IOPUB: [('status', {'execution_state': 'busy'}),
        ('execute_input', {...}),
        ('error', {'ename': 'ExecutionError',
                    'evalue': 'Cell execution failed (exit code 1)',
                    'traceback': [...]}),
        ('status', {'execution_state': 'idle'})]
```

Even the semantically-valid `%%mode interpreter` (switching to the already-active
default lane, a no-op in principle) fails the same way, because `%%mode` is never
stripped before the cell body reaches `bin/simple`.

## Root cause

`src/app/jupyter_kernel/main.spl` does not import `std.notebook.magics` at all
(`use` list at the top of the file has no `magics` entry), and its only
execute-path function calls the session manager with the override hardcoded to
`""`:

```
fn session_execute(code: text, exec_count: i64) -> (text, text, bool):
    val result: CellResult = SESSION_MANAGER.execute_cell(DEFAULT_SESSION_ID, code, "cell_{exec_count}", "")
```

`KernelSessionManager.execute_cell`'s 4th parameter (`cell_override`) is exactly
the slot `magics.parse_magics(...).cell_mode_override` is meant to fill (see
`session_manager.spl:157` and `resolve_cell_mode`/`resolve_mode` right above it),
but nothing in `main.spl` ever calls `parse_magics`, so:

- `%%mode`/`%mode` never switch lanes — `code` (including the magic line itself)
  is always run verbatim on the session's hardcoded `"interpreter"` default
  (`session_init()` calls `SESSION_MANAGER.create_session(DEFAULT_SESSION_ID,
  "interpreter")` and nothing ever changes it).
- `%lanes`, `%reset`, `%budget`, `%timeout`, `%onfault` are likewise parsed by
  `magics.spl` but never consulted by the kernel.
- Any magic line left in cell source (because it was never stripped) is handed
  straight to the compiler, so a cell that legitimately uses a magic **fails to
  compile** instead of being honored or cleanly rejected.

This means Stream K's `RemoteExec`/`CudaExec`/`VulkanExec` lanes (K4/K5/K6) are
unreachable from the actual Jupyter kernel today, even where the underlying
adapter (K4, landed) works correctly in isolation — matches the repo's recurring
"wired but unreachable" pattern (see `reference_iso_ownership_pipeline_works_but_is_unreachable_from_source.md`
for the general shape of this class of defect).

## How it was found

While building Stream P's P3 Docker E2E fixtures/script
(`doc/03_plan/agent_tasks/notebook_lanes_parallel_plan_2026-08-07.md`), a
`mode_local.ipynb` fixture used a `%%mode interpreter` first line (mirroring the
design doc's magic syntax). It failed to execute inside a real containerized
kernel session (`jupyter nbconvert --execute` against `tools/jupyter/kernel.json`
+ `kernel_wrapper.py` + `src/app/jupyter_kernel/main.spl`, verified against a
freshly-pulled `python:3.11-slim` image with `jupyter_client`/`pyzmq` installed).
Isolating the failure: the exact same code without the `%%mode` line executed
correctly and printed `42`; re-adding only `%%mode interpreter` reproduced the
`exit code 1` failure. Manual driver used for isolation:

```python
km = jupyter_client.KernelManager(kernel_name="simple")
km.start_kernel(...)
kc = km.client(); kc.start_channels(); kc.wait_for_ready(timeout=30)
kc.execute("%%mode interpreter\nval x = 21\nprint x * 2")  # fails
kc.execute("val x = 21\nprint x * 2")                       # succeeds, prints 42
```

## Fix direction (not landed — out of scope for P3, which is fixtures/Docker-script only)

In `src/app/jupyter_kernel/main.spl`:
1. `use std.notebook.magics.{parse_magics}` (and whatever accessor types it
   exposes).
2. In `session_execute` (or wherever `execute_request` content is first
   handled), call `parse_magics(code)` before dispatch; on `.error != ""`,
   report it as a normal cell error instead of forwarding to the compiler; on
   success, pass `.code` (the magic-stripped remainder) as the `code` argument
   and `.cell_mode_override` as the 4th argument to
   `SESSION_MANAGER.execute_cell`.
3. Wire `%mode` similarly to `KernelSession`'s persistent default (probably via
   a new `SESSION_MANAGER.set_default_mode(...)` call — `session_manager.spl`
   already exposes the pieces resolve_mode/resolve_cell_mode need).
4. `%lanes`, `%reset`, `%budget`, `%timeout`, `%onfault` need their own
   dispatch out of `parse_magics`'s result — currently none of that is called
   either.

## Impact on Stream P/K verification

`scripts/test/jupyter-docker-test.shs` (P3) can only exercise the **local**
lane end-to-end today; it cannot use a `%%mode`/`%%mode`-driven cell to
actually route a fixture through K4's `RemoteExec` QEMU RV32 adapter via the
real kernel, because the magic that would trigger that routing never reaches
`session_manager`. `test/03_system/tools/jupyter/fixtures/mode_qemu_rv32.ipynb`,
`mode_cuda.ipynb`, and `mode_vulkan.ipynb` therefore carry their intended lane's
mode-spec string only in notebook/cell **metadata** (`simple_lane.mode_spec`),
not as executable `%%mode` magic, and their code cells are plain valid Simple
source that runs on the default local lane — they are structural fixtures for
once this bug is fixed, not lane-routing proofs today.
