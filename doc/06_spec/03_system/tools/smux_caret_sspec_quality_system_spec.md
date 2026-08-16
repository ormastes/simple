# smux and LLM Caret SSpec Quality — System Scenario Manual

> **Hand-authored, pending docgen.** `simple spipe-docgen` could not be run for
> this manual: no admitted pure-Simple CLI exists in-tree (see
> `doc/08_tracking/bug/deployed_selfhost_test_subcommand_segv_blocks_bootstrap_2026-08-16.md`).
> Regenerate this file from
> `test/03_system/tools/smux_caret_sspec_quality_system_spec.spl` once a
> qualified runner is admitted; the executable spec is the source of truth.

**Executable spec:** `test/03_system/tools/smux_caret_sspec_quality_system_spec.spl`
**Plan:** `doc/03_plan/sys_test/smux_caret_sspec_quality.md`
**Status:** `TEST_BLOCKED` for admitted evidence — spec is complete, fail-closed,
and observed passing 13/13 under the non-admitted seed runner only.

## Purpose

A legacy `fn test_*` + `print("PASS: ...")` spec executes **zero examples**. The
fail-closed zero-examples gate therefore holds it permanently RED while its own
prints claim success, and a `FAIL` print never fails the process — such checks
are not oracles at all.

This scenario reads the lane's committed spec sources and asserts they are
Modern SSpec: `describe`/`it` blocks carrying `expect(...)` oracles, no
`fn test_*`, no `main()`-driven prints, and byte-identical mirror trees.

## Fail-closed construction

The manual makes no claim that is not asserted by the executable spec.

- A spec file that is **missing, unreadable, or empty** classifies as *not
  modern* and **fails** its example. It is never skipped, never counted a pass.
- The classifier is itself proven to **discriminate** (SSQ-CLS-001/002) before
  it is trusted against real files, so a green run cannot come from a vacuous
  oracle that returns `true` for everything.
- An example that declares no oracle is rejected, so a `describe`/`it` shell
  with no `expect(...)` cannot pass.

## Requirements covered

| ID | Statement |
|---|---|
| REQ-SSQ-001 | The quality classifier distinguishes Modern SSpec sources from legacy print-based sources. |
| REQ-SSQ-002 | The classifier rejects empty, oracle-free, and missing sources rather than passing vacuously. |
| REQ-SSQ-003 | smux and LLM Caret unit specs are Modern SSpec with no surviving legacy construct. |
| REQ-SSQ-004 | The smux dashboard unit spec is Modern SSpec with no surviving legacy construct. |
| REQ-SSQ-005 | Duplicate test trees (`test/01_unit` and `test/unit`) stay byte-identical. |
| NFR-SSQ-001 | Neither duplicate tree may regress alone; the mirror is classified independently. |

## Scenarios

| Scenario | Class | Owner |
|---|---|---|
| SSQ-CLS-001 | executable | this spec — classifier discriminates modern from legacy |
| SSQ-CLS-002 | executable | this spec — classifier rejects empty and oracle-free sources |
| SSQ-SMUX-001 | executable | `test/01_unit/os/smux_spec.spl` |
| SSQ-SMUX-002 | executable | `test/01_unit/os/smux/smux_dashboard_spec.spl` |
| SSQ-MIRROR-001 | executable | `test/unit/os/smux_spec.spl` |
| SSQ-CARET-001 | executable | `test/01_unit/app/llm_caret/agent_files_spec.spl` |

## Scenario flow

### SSQ-CLS — the quality classifier discriminates

**should classify a legacy print-based spec as legacy, not modern** — REQ-SSQ-001
1. *Classify a synthetic legacy main()-driven source.*
   Expect one `fn test_*`, two PASS/FAIL prints, zero examples; legacy, not modern.

**should classify a synthetic modern spec as modern** — REQ-SSQ-001
1. *Classify a synthetic describe/it source carrying oracles.*
   Expect one `describe`, one `it`, one `expect`; modern, not legacy.

**should refuse an empty source rather than passing vacuously** — REQ-SSQ-002
1. *Classify an empty source.* Expect zero examples and a non-modern verdict.

**should refuse examples that declare no oracle** — REQ-SSQ-002
1. *Classify a describe/it source with no `expect(...)` call.*
   Expect one example, zero oracles, and a non-modern verdict.

**should treat a missing file as a failure, never as a skip** — REQ-SSQ-002
1. *Classify a path that does not exist.* Expect `present == false` and non-modern.

### SSQ-SMUX — the smux unit specs are Modern SSpec

**should carry describe/it oracles and no legacy constructs in smux_spec** — REQ-SSQ-003
1. *Read the committed smux unit spec.* Expect it to exist.
2. *Assert it is Modern SSpec with no surviving legacy construct.*
   Expect zero `fn test_*`, zero PASS/FAIL prints, no `main()`, modern verdict.

**should declare at least the twenty converted smux examples** — REQ-SSQ-003
1. *Read the committed smux unit spec.* Expect exactly 20 examples.

**should carry describe/it oracles and no legacy constructs in the dashboard spec** — REQ-SSQ-004
1. *Read the committed smux dashboard unit spec.* Expect it to exist.
2. *Assert it is Modern SSpec with no surviving legacy construct.*

**should declare at least the twenty-one converted dashboard examples** — REQ-SSQ-004
1. *Read the committed smux dashboard unit spec.* Expect exactly 21 examples.

### SSQ-MIRROR — duplicate test trees stay identical

**should keep the smux mirror byte-identical to its 01_unit original** — REQ-SSQ-005
1. *Read both copies of the smux unit spec.* Expect both to exist.
2. *Compare the two sources byte for byte.* Expect equality.

**should keep the dashboard mirror byte-identical to its 01_unit original** — REQ-SSQ-005
1. *Read both copies of the smux dashboard unit spec.* Expect both to exist.
2. *Compare the two sources byte for byte.* Expect equality.

**should keep the mirror modern too, so neither tree regresses alone** — NFR-SSQ-001
1. *Classify the mirrored smux spec independently.* Expect modern, 20 examples.

### SSQ-CARET — the LLM Caret lane specs are Modern SSpec

**should find no legacy print-based construct in the caret unit spec** — REQ-SSQ-003
1. *Read a committed LLM Caret unit spec.* Expect it to exist.
2. *Assert the caret lane carries oracles, not prints.* Expect modern verdict.

## Execution status

`TEST_BLOCKED` for admitted evidence. The spec **does execute and pass** —
observed `declared>=13 executed=13 passed=13 failed=0 dropped=0` — but that run
came from `bin/release/x86_64-unknown-linux-gnu/simple`, which self-identifies
as the Rust bootstrap seed and is **not an admitted pure-Simple runner**. The
run is recorded as a development observation, not as acceptance evidence, and
the lane is not marked green on it.

Why no admitted runner exists here:

- the tracked self-hosted `release/x86_64-unknown-linux-gnu/simple` segfaults in
  its `test` subcommand (exit 139, no output)
- `bootstrap/stage1|2|3/simple` expose no `test` subcommand, and cannot lower the
  SSpec DSL (`unresolved name: describe / it / expect`)
- `build bootstrap` terminates inside Stage 1 without a verdict, so the
  documented recovery path is itself blocked

Upstream record:
`doc/08_tracking/bug/deployed_selfhost_test_subcommand_segv_blocks_bootstrap_2026-08-16.md`.
`spipe-docgen` and `sspec-maintain scan` were likewise not run. No placeholder
pass is recorded anywhere in this lane.

Run once a qualified runner is admitted:

```
bin/simple test test/03_system/tools/smux_caret_sspec_quality_system_spec.spl
```
