# smux / LLM Caret SSpec Quality Feature Expert

## Authority and boundaries

This feature owns **spec quality** for the smux and LLM Caret lanes — the shape
of the test files, not the runtime behaviour they describe. smux session,
window, pane, layout and dashboard semantics belong to the smux feature; agent
messaging, provider transport and CLI parity belong to the LLM Caret features.

The authority for what "modern" means is `.claude/rules/testing.md` (Modern
SSpec) plus `doc/07_guide/infra/sspec_antipatterns.md`. This expert does not
redefine either; it applies them to two specific lanes and guards the result.

## The defect this feature exists to prevent

A spec written as `fn test_*` bodies printing `PASS`/`FAIL` and driven by
`main()` executes **zero examples**. Consequences, all of which have happened
here:

- The fail-closed zero-examples gate holds the file permanently RED —
  `declared>=1 executed=0 passed=0 failed=1 reason=zero-examples` — regardless
  of what it prints.
- A `FAIL` print does not fail the process, so the printed output and the
  verdict can disagree, and humans read the printed side.
- The checks are therefore not oracles. Converting them is not cosmetic.

## Review invariants

- **`executed` is the number that matters.** A conversion that leaves
  `executed=0` did not take, whatever the file prints. Never accept a PASS line
  as evidence.
- **Every example carries an oracle.** A `describe`/`it` shell with no
  `expect(...)` is the same vacuity in a new costume.
- **Both mirror trees move together.** `test/01_unit/**` and `test/unit/**` are
  duplicated; convert both identically and verify with `cmp`, never by eye.
  A one-sided edit turns `check-test-tree-divergence` red.
- **Missing evidence fails, never skips.** In the system spec, an absent or
  unreadable spec file classifies as not-modern and fails its example.
- **The classifier proves itself first.** Before judging real files it must
  classify a synthetic legacy source as legacy and a synthetic modern source as
  modern, and reject empty and oracle-free sources. Otherwise a green run
  proves nothing.
- **No placeholder passes.** If the runtime is unavailable, record
  `TEST_BLOCKED` honestly and leave the spec fail-closed.

## Known trap: do not chain off a static factory

```simple
expect(PaneId.create(0, 80, 24).area()).to_equal(1920)   # fails to resolve
```

fails with `semantic: method 'area' not found on value of type object in nested
call context` — the receiver's declared type erases to `object` inside a nested
call. Bind a `val` first. This is a compiler defect
(`doc/08_tracking/bug/static_factory_method_chain_wrong_value_2026-08-16.md`),
not a style preference; 9 of 20 examples in one file failed for it alone. Do not
"fix" it by loosening the assertion.

## Known trap: module-level `var` is stale inside an `it`

An `it` closure captures a module-level `var` by value, so a direct read inside
an example returns the initial value regardless of mutation. Read through a
function instead. Filed as `doc/08_tracking/bug/module_var_stale_in_it_closure_2026-08-16.md`.

This matters because legacy specs commonly hold their test doubles in mutable
module state. In `smux_system_spec.spl` it silently broke 4 of 56 metrics
examples; the fix is the `_get_metrics()` accessor.

## Evidence rules for this lane

The seed (`bin/release/<triple>/simple`, which prints a bootstrap-seed warning)
is **not** an admitted runner. A seed-produced green may be recorded only with
the caveat attached, and never as self-hosted proof. Runtime, `spipe-docgen`
and `sspec-maintain scan` require an admitted pure-Simple CLI. At the time of
writing none exists in-tree — the tracked self-hosted binary segfaults in
`test` and the re-bootstrap recovery path is itself blocked
(`deployed_selfhost_test_subcommand_segv_blocks_bootstrap_2026-08-16.md`).

## Map

| Concern | Where |
|---|---|
| Lane state and ACs | `.spipe/smux_caret_sspec_quality/state.md` |
| System test plan | `doc/03_plan/sys_test/smux_caret_sspec_quality.md` |
| Executable system spec | `test/03_system/tools/smux_caret_sspec_quality_system_spec.spl` |
| Scenario manual (Markdown only) | `doc/06_spec/03_system/tools/smux_caret_sspec_quality_system_spec.md` |
| Conversion recipe | `doc/07_guide/infra/sspec_legacy_migration.md` (worked example 3) |
| Converted unit specs | `test/01_unit/os/smux_spec.spl`, `test/01_unit/os/smux/smux_dashboard_spec.spl` (+ mirrors) |
| Converted system spec | `test/03_system/tools/smux_system_spec.spl` (56 examples, 13 REQ groups) |

## Converted inventory

| Spec | Examples |
|---|---|
| `test/01_unit/os/smux_spec.spl` (+ mirror) | 20 |
| `test/01_unit/os/smux/smux_dashboard_spec.spl` (+ mirror) | 21 |
| `test/03_system/tools/smux_system_spec.spl` | 56 |
| `test/03_system/tools/smux_caret_sspec_quality_system_spec.spl` (new guard) | 15 |

No legacy print-based spec remains in the smux or LLM Caret lanes. The quality
guard asserts this and fails if one reappears.
