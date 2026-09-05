# Guide C — audit every `[x]` that cites a plan-acceptance spec

Owner: one haiku/sonnet-class agent. Read-only on `src/`; edits only under
`doc/03_plan/`. Follow literally.

## Status of the three named false ticks (checked at HEAD 2026-09-05)

All three are already corrected in the committed tree — do NOT re-edit them:

- `doc/03_plan/language/gpu_fpga/sycl_parity_unified_kernel_plan_2026-06-13.md:88`
  — now `- [ ] W3.2 ... NOT verified`: `decl_set_unroll_factor/pipeline_ii/memory_banks`
  are only `use`d at `src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl:25`,
  zero call sites. (The import is also unused code; the fix is to WIRE it — see
  Decision point 2 — never to delete the import to silence a lint.)
- `doc/03_plan/infra/perf_umbrella/perf_checklists.md:212` — citation replaced;
  the new one resolves (`syscall_shim_process.spl:338`, `user_entry_bridge.spl:21-24`,
  `vmm_address_space.spl:314` all read as quoted).
- `doc/03_plan/compiler/aspect_dynload/aspect_dynload_lane_plan_2026-08-19.md:401`
  — now `- [ ] ... NOT verified`.

## The remaining work — the broad weakness

Many `[x]` lines cite an acceptance spec that is itself red. A tick that cites a
red spec is a false tick.

1. Build the list:
   `grep -rn "\[x\].*test/03_system/plan_acceptance/" doc/03_plan > build/tick_audit/list.txt`
   (create the dir first). Also include ticks whose line or the next indented
   line names such a spec.
2. For each DISTINCT spec named, run it once:
   `SIMPLE_BINARY=$PWD/src/compiler_rust/target/debug/simple src/compiler_rust/target/debug/simple run <spec> > build/tick_audit/<basename>.log 2>&1`
   Record the `SPEC FILE VERDICT` line. Discard (and re-run after noting it) any
   log containing `E1034`.
3. For each tick: if the cited spec's verdict is `outcome=OK`, leave the tick.
   If the verdict is `ERROR`/`NOT_RUN`, or the specific `it` named on the tick
   line shows `✗`, change `[x]` to `[ ]` and append on the same line:
   `— UNTICKED 2026-09-05: cited spec <path> is red (<verdict line>); re-tick only when its it passes`.
4. Never change any other text on the line. Never delete a line.

## Decision points

1. A tick that cites a spec's `it` by name where that `it` is `✓` while OTHER
   `it`s in the file are `✗`: leave the tick, but append
   `— cited it verified ✓ 2026-09-05; file-level verdict is red for other its`.
2. For the sycl W3.2 box: its acceptance `it` now exists —
   `test/03_system/plan_acceptance/sycl_parity_unified_kernel_plan_spec.spl`
   "W3.2 frontend decorator wiring — @unroll/@pipeline/@memory on a kernel fn
   reach the AST decl through the real parser" (RED: `expected 0 to equal 2`).
   Do not implement it in this guide; file a `doc/08_tracking/bug/` record
   naming `enum_module_body.spl:25`, the setters at
   `_Ast/decl_nodes.spl:1260-1278`, that `it`, and the unblock condition
   "`grep -rn 'decl_set_unroll_factor(' src/compiler` returns a call site
   inside the decorator parse path and the W3.2 `it` passes".
3. Unticking a box can make a plan's open-box count exceed its spec's `it`
   count, which turns `check-plan-acceptance-coverage.shs` RED
   (`short:<slug>(its/boxes)`). Report the shortfall with the slug; the lead
   writes the missing `it` (as was done for sycl W3.2 on 2026-09-05).

## Acceptance

- `build/tick_audit/list.txt` exists and is non-empty (control: if it is empty
  your grep is wrong — there are known citations, e.g. in
  `doc/03_plan/agent_tasks/plan_remains_acceptance_2026-09-05.md`).
- Every untick line carries the `— UNTICKED 2026-09-05:` suffix with a verdict
  line pasted from a log under `build/tick_audit/`.
- `sh scripts/check/check-plan-acceptance-coverage.shs` still prints
  `PASS — 36 plan(s) checked, 0 uncovered` (unticking ADDS open boxes; if a plan
  now has more open boxes than its spec has `it`s, report the shortfall — do not
  add `it`s and do not re-tick).

## Checkbox rule

Tick plan item C ONLY when the three acceptance bullets hold, appending
`— verified <count> ticks audited, <count> unticked, coverage PASS line, <date>`.
