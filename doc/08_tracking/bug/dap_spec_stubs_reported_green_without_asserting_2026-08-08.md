# DAP spec examples reported GREEN while asserting nothing (2026-08-08)

Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

## Summary

Four DAP unit spec files under `test/01_unit/app/dap/` contained 58 `it`
examples whose entire body was a descriptive comment plus `assert_true(true)`.
Each example reported `passed` even though it exercised nothing about the
described behaviour — a pure false-green cluster.

| File | Vacuous examples |
|------|-------------------|
| `test/01_unit/app/dap/adapter_unification_spec.spl` | 21 |
| `test/01_unit/app/dap/breakpoints_spec.spl` | 9 |
| `test/01_unit/app/dap/protocol_spec.spl` | 13 |
| `test/01_unit/app/dap/server_spec.spl` | 15 |
| **Total** | **58** |

Baseline run (original stub content, `bin/simple test <spec> --no-session-daemon`):

```
adapter_unification_spec: Results: 21 total, 21 passed, 0 failed
breakpoints_spec:         Results: 9 total, 9 passed, 0 failed
protocol_spec:             Results: 13 total, 13 passed, 0 failed
server_spec:                Results: 15 total, 15 passed, 0 failed
```

## Fix approach

Every stub was replaced with a genuine assertion that reads the real
implementation source (`rt_file_read_text`) and checks for a specific,
sabotage-provable line or block of that source via `to_contain`. This matches
the pattern already used by non-stub sibling specs in the same directory
(`dap_spec.spl`, `interpreter_hooks_spec.spl`,
`server_hooks_integration_spec.spl`), which check source text rather than
instantiating the DAP classes directly.

The canonical implementation checked is `src/lib/nogc_sync_mut/dap/*` (the
same tree the pre-existing sibling specs already reference), plus
`src/lib/nogc_async_mut/debug/coordinator.spl` for `VarInfo`. Note: `src/app/dap/*`
is a near-duplicate tree (protocol.spl / adapter/mod.spl / adapter/local.spl
are byte-identical; breakpoints.spl and server.spl differ only in a few
import paths and a native-codegen `Dict.get()` workaround) — this doc's line
references are to the `nogc_sync_mut` copy.

Per-file disposition:

| File | Implemented (real, exercises actual behaviour) | Left RED (spec is correct, impl is missing) |
|------|---|---|
| `adapter_unification_spec.spl` | 21 | 0 |
| `breakpoints_spec.spl` | 7 | 2 |
| `protocol_spec.spl` | 11 | 2 |
| `server_spec.spl` | 14 | 1 |
| **Total** | **53** | **5** |

Nothing was deleted — every described behaviour maps either to real code
(implemented) or a genuine, filed gap (left RED). Zero `assert_true(true)`
remain in the four files.

Post-fix run (`bin/simple test <spec> --no-session-daemon`):

```
adapter_unification_spec: Results: 21 total, 21 passed, 0 failed
breakpoints_spec:         Results: 9 total, 7 passed, 2 failed
protocol_spec:             Results: 13 total, 11 passed, 2 failed
server_spec:                Results: 15 total, 14 passed, 1 failed
```

Total: 58 examples, 53 passed (with real assertions), 5 correctly RED.

## The 5 LEAVE-RED entries (genuine gaps, not test bugs)

Each of these asserts the behaviour the stub's own comment described. The
assertion fails honestly because the described behaviour does not exist yet
in the implementation.

1. **`test/01_unit/app/dap/breakpoints_spec.spl:33` "adds hit condition to
   breakpoint"** — `BreakpointEntry` has a `hit_condition: Option<String>`
   field (`src/lib/nogc_sync_mut/dap/breakpoints.spl:12`) and
   `check_breakpoint_condition()` reads it, but unlike `with_condition()`
   there is no `with_hit_condition()` builder, and
   `BreakpointManager.set_breakpoints()` (same file, ~line 53) never
   populates `hit_condition` from the incoming `SourceBreakpoint` at all —
   only `condition` is wired through. **Unblock:** add a
   `with_hit_condition(hit_condition: String) -> BreakpointEntry` builder and
   call it from `set_breakpoints()` when `source_bp.hit_condition` is
   `Some`.

2. **`test/01_unit/app/dap/breakpoints_spec.spl:82` "clears all
   breakpoints"** — `BreakpointManager.clear_breakpoints(source_path)`
   (`src/lib/nogc_sync_mut/dap/breakpoints.spl:81`) only clears the entries
   for one source path; there is no method that clears every breakpoint
   across all sources in the manager. **Unblock:** add a
   `clear_all_breakpoints() -> Nil` method that resets
   `self.breakpoints` to `{}`.

3. **`test/01_unit/app/dap/protocol_spec.spl:52` "creates arguments
   scope"** — `DapServer.handle_scopes()`
   (`src/lib/nogc_sync_mut/dap/server.spl:189`) only ever emits
   `Scope.new("Local", 1)`, `Scope.new("Global", 2)`, and conditionally
   `Scope.new("Registers", 3)`. There is no distinct "Arguments" scope,
   even though `handle_variables()`'s scope==2 branch
   (`dap_handlers.spl:105-108`) comments that ref=2 means "arguments" for
   remote backends and "globals" for local. **Unblock:** either emit a real
   `Scope.new("Arguments", N)` from `handle_scopes()` for adapters that
   distinguish arguments from globals, or drop the DAP-spec expectation that
   a distinct Arguments scope exists for this implementation and reword the
   VS Code integration docs accordingly.

4. **`test/01_unit/app/dap/protocol_spec.spl:65` "creates variable with
   children"** — `dap_handlers.spl`'s `handle_variables()` (nested-ref
   branch, ~line 150) calls `pvar.with_children(child.name.hash())` on a
   `protocol.DapVariable` instance, but `DapVariable`
   (`src/lib/nogc_sync_mut/dap/protocol.spl:164`) never defines
   `with_children()` — only the unrelated `dap_types.VariableInfo` class
   does (`src/lib/nogc_sync_mut/dap/dap_types.spl:102`). This is a latent
   defect independent of the false-green cluster: the nested-variable-
   expansion code path calls an undefined method on `DapVariable`.
   **Unblock:** add `DapVariable.with_children(variables_reference: Int) ->
   DapVariable` (mirroring `VariableInfo.with_children`) in `protocol.spl`.

5. **`test/01_unit/app/dap/server_spec.spl:29` "handles attach request"**
   — `DapServer.handle_request()`'s command `match`
   (`src/lib/nogc_sync_mut/dap/server.spl:444`) has no `"attach"` case at
   all — only `"launch"`. A DAP `attach` request currently falls through to
   the unknown-command branch and gets a failure response. **Unblock:** add
   a `handle_attach()` handler (attach without spawning a new process) and
   wire a `case "attach":` arm into `handle_request()`.

## Other findings from this investigation (not fixed here, out of scope)

- **`full()` capabilities intentionally exclude reverse debugging.**
  `AdapterCapabilities.full()` (`adapter/mod.spl`) sets every flag `true`
  except `supports_reverse: false`; only `replay()` sets
  `supports_reverse: true`. The original stub's comment ("full() … has
  everything enabled") was simply inaccurate — this looks like deliberate
  design (live full-featured hardware adapters vs. a record/replay backend),
  not a defect, so the rewritten assertion documents the real behaviour
  instead of the stub's claim.
- **The vacuous-stub pattern is broader than these 4 files.** Sibling specs
  in the same directory that are *not* flagged as false-green in this task
  (e.g. `debug_configuration_spec.spl`, `debug_session_spec.spl`,
  `debug_state_spec.spl`) use a related but distinct anti-pattern: `val x =
  true; assert_true(x)` / `val name = "Debug Simple"; assert_true(name ==
  "Debug Simple")` — a locally-hardcoded literal compared to itself, which
  is equally incapable of failing. These were left untouched (out of scope
  for this task) but are worth a follow-up sweep.
- **No `BreakpointStore` class exists anywhere in the repo.** The original
  `breakpoints_spec.spl` was titled around a `BreakpointStore` type; the real
  class is `BreakpointManager` (`src/lib/nogc_sync_mut/dap/breakpoints.spl`
  and the near-duplicate `src/app/dap/breakpoints.spl`). Confirmed by
  scoped search of `src/app/dap`, `src/lib/nogc_sync_mut/dap`, and
  `src/lib/nogc_async_mut/dap` — zero hits. The rewritten spec renames the
  `describe` block to match reality.

## Verification performed

- Baseline (`assert_true(true)` stubs) captured for all 4 files: all green,
  matching the given verified facts (21/9/13/15 examples, 0 failures).
- Post-fix run captured for all 4 files: 53 passed, 5 correctly RED.
- Sabotage-probed 3 of the newly-implemented (green) assertions by breaking
  the *implementation* (not the spec) and confirming each specific assertion
  turned RED, then reverted and confirmed GREEN again:
  1. `src/lib/nogc_sync_mut/dap/adapter/local.spl`: changed
     `.with_watchpoints(1024)` → `.with_watchpoints(512)` (both call sites,
     via `sed`). `adapter_unification_spec.spl` went from 21/21 to 19/21,
     failing exactly `local adapter has max_watchpoints 1024` and `local
     adapter does not support registers` (the latter shares the same
     asserted multi-line chain). Reverted → back to 21/21.
  2. `src/lib/nogc_sync_mut/dap/server.spl`: renamed
     `self.adapter.resume()?` → `self.adapter.resume_broken()?` inside
     `handle_continue()`. `server_spec.spl` went from 14/15 (1 known RED) to
     13/15, newly failing `handles continue request`. Reverted → back to
     14/15 (only the known `handles attach request` RED remained).
  3. `src/lib/nogc_sync_mut/dap/protocol.spl`: changed `DapVariable.new()`'s
     `variables_reference: 0` → `variables_reference: 99`.
     `protocol_spec.spl` went from 11/13 (2 known RED) to 10/13, newly
     failing `creates simple variable`. Reverted → back to 11/13 (only the
     two known REDs remained).
- Confirmed zero `assert_true(true)` remain in the 4 spec files
  (`grep -c "assert_true(true)"` → 0 for all).
- Confirmed no stray diffs were left in `src/lib/nogc_sync_mut/dap/*` after
  the sabotage probes (`git status --short` clean on those paths).
