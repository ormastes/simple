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

## Regression and repair — 2026-08-24

The claim above ("no legacy print-based spec remains") was true when written and
**false in the tree for weeks**. All three converted specs had been clobbered
back to the legacy shape by later commits, while the lane state file still
recorded every AC as DONE:

| spec | converted at | clobbered by | symptom |
|---|---|---|---|
| `test/03_system/tools/smux_system_spec.spl` | `aa94bed2717` | `376031072c5` | RED under the zero-examples gate (`executed=0 dropped=1`) |
| `test/01_unit/os/smux_spec.spl` | `76c0f2f0837` | `f13adc2eca5` | 20 `fn test_*` helpers re-added; every oracle reduced to `expect(test_x()).to_equal(true)` |
| `test/01_unit/os/smux/smux_dashboard_spec.spl` | `76c0f2f0837` | `f13adc2eca5` | same, 21 helpers |

All three restored. `smux_caret_sspec_quality_system_spec` went **10/15 -> 15/15**.

**The guard was never the problem.** AC-4's fail-closed system spec detected
every one of these correctly; nothing was reading its verdict. A converted-spec
inventory in a wiki page or state file is a claim about a moment, not a
standing fact — only a scheduled run of the guard makes it standing. That is the
open process gap.

### Documentization score, and its ceiling

Both unit specs were raised **74 -> 91** by authoring what the scorer asks for:
a purpose/audience/workflow/limitations docstring, ordered `step(...)` narration,
a same-line `# oracle:` rationale per numeric expected value, REQ ids bound
inside scenario bodies, and lifecycle links that resolve. narrative, structure
and oracle are all at 100 and the `SSDOC-TRC-003` blocker is cleared.

**91 is the generator's ceiling, not the specs'.** The last 9 points are
`SSDOC-EVD-002` and `SSDOC-MNT-008`, both charged against a spec for what
`documentize.spl` failed to render — it copies scenario bodies verbatim, so
`step(...)` appears as literal source and no traceability section is emitted.
Filed: `doc/08_tracking/bug/sspec_docgen_dumps_source_instead_of_scenario_manual_2026-08-24.md`.

Authoring trap: `SSDOC-ORA-003` matches `# oracle:` only on the **same line** as
the assertion. A marker on the preceding line silently does nothing.

Full audit: `doc/09_report/caret_smux_slang_agent_manager_gap_audit_2026-08-24.md`.
