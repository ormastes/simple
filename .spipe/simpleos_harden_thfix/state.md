# Lane THFIX2 (team COMPILER) — state 2026-07-27

## Job A — module_registry.spl adjudication: NOT VERIFIED, do not land as-is
- Change is on a file ANOTHER SESSION IS ACTIVELY EDITING (it flipped
  `.push()` -> `x = x.push()` mid-lane, citing "stage-4 repro19 segfault").
  Do not edit concurrently; hand findings to the owning lane.
- Mechanism works: standalone shape probe `build/thfix_reg_probe.spl` — 2/2
  entries, cross-module accessor reads correct, nested Dict fields survive.
- NOT exercised by any tier. `build/native_probe/simple` = Jul 23,
  `bin/release/.../simple` = Jul 25; the edit is Jul 27. Compiler-source
  changes need a rebuild to be observed. Command (NOT run, per no-bootstrap
  rule): `bin/simple build bootstrap`.
- DEFECT: `hir_registry_put` appends unconditionally -> first-wins on repeat,
  while the Dict it replaced and the sibling `entry_modules[name] = m`
  (driver.spl:689) are last-wins. driver.spl:685 fills from the
  NON-deduplicated `entry_sources` (the deduped list is `unique_entry_sources`,
  :657), so repeats are expected: unbounded growth + registry/ctx.modules
  divergence. Fix: overwrite when `_hir_registry_index(name) >= 0`.
- Cited doc does NOT support the array rationale. The bug doc's Round 5
  prescribes a Dict-backed registry ("plain arg-pass + dict-insert"); the
  "Dict-typed globals lower to uninitialized allocas" claim is uncited and
  contradicted by working Dict module-globals in the compiler
  (mir_data.spl:644/667/668/686/687/709, bootstrap_globals.spl:120).

## Job B — two-hop mutation loss: ROOT-CAUSED
Interpreter place-model limit (2 levels, variable-rooted). Loud on assignment
(`node_exec.rs:944-947`), silent on the method-call receiver path. JIT is
correct. Cross-module correlation was an artifact: mutating `fn X(self)` in
`src/lib/nogc_sync_mut/ecs/**` is a hard HIR error that bails the JIT for the
whole program, so ecs consumers run interpreted. Full writeup appended to
`doc/08_tracking/bug/selfhost_two_hop_field_method_mutation_lost_2026-07-27.md`.
Regression spec: `test/01_unit/compiler/two_hop_field_method_mutation_spec.spl`
(+ `test/fixtures/two_hop_mutation/inner_types.spl`) — 5 examples, 4 failures,
deliberately RED. `tty_termios_ld_spec.spl` PASS (unchanged).

## Not committed (per lane brief). No compiler semantics changed.
