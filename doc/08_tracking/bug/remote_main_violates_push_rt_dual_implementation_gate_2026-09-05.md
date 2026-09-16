# `origin/main` violates its own blocking push gate — nobody can push cleanly

## Status

Open. Not caused by any one lane's in-flight work: the offending symbols are
already committed at the remote tip, so the gate fails for **every** push from
any tree based on it.

## Symptom

`push-rt-dual-implementation` is a **blocking** push-tier gate
(`config/check/must_check_gates.sdn`). Against remote `main` it reports:

```text
NEW single-lane rt_* (adding one violates the directive — implement the
missing lane in C and Simple with an alias, do not regenerate the baseline):
  rt_phase_profile_record
  rt_to_int_dynamic
  rt_vulkan_copy_u32_slots
  rt_vulkan_readback_u32_checksum
FAIL — 2492 symbol(s) checked against 2488 baselined, 4 new, 0 stale
push-must-check: BLOCKING gate push-rt-dual-implementation failed (exit 1)
```

## The symbols predate any current work

Measured 2026-09-05 against `320e6d99e4b` (remote `main` at the time):

| symbol | files at the base |
|---|---|
| `rt_phase_profile_record` | 2 |
| `rt_to_int_dynamic` | 2 |
| `rt_vulkan_copy_u32_slots` | 4 |
| `rt_vulkan_readback_u32_checksum` | 4 |

All four are present **before** any local commit is applied. The `rt_vulkan_*`
pair arrives with `320e6d99e4b perf(bench): C Vulkan 2D reference vs Simple
Engine2D benchmark + NFR gate (#346)`. The gate is tree-scoped, not
range-scoped, so it evaluates the whole tree and fails regardless of what a
push contains.

## Why this went unnoticed

The must-check pre-push hook was **not installed** on this machine
(`install-must-check-hooks.shs --check` → `NOT INSTALLED OR OUTDATED`). Every
push from here was reaching the remote with defective guard wiring — the exact
fail-open condition
`doc/08_tracking/bug/fourth_tree_wipe_6f86ff32a7d_guard_not_enforced_2026-08-11.md`
describes. The gate only became visible after the hook was installed on
2026-09-05, at which point it immediately and correctly refused a push.

So the ordering is: the debt landed while nothing was enforcing, and the first
push after enforcement was restored is the one that pays for it.

## Required resolution

Implement the missing lane (C or Simple, with an alias) for each of the four
symbols, per the gate's own directive. **Do not run `--generate-baseline`** —
the gate explicitly forbids absorbing new debt that way, and doing so would
convert a loud, correct failure into a silent one.

Owner: the lane that landed `#346` and the profiling/`to_int_dynamic` changes.

## Bypass record (required by `.claude/rules/vcs.md`)

The parser-sharing range was pushed on 2026-09-05 with `--no-verify`, on the
user's explicit instruction, after establishing that the blocker is not that
range's:

- the range introduces **none** of the four symbols
  (`git diff <base>..<tip>` contains no `+` line adding any of them);
- all four exist at the base the range sits on;
- the three mandatory tree guards were run by hand with an explicit
  `<base>..<tip>` range and all PASS non-vacuously — `check-no-conflict-tree-push`
  (11 commits, 11 trees, 0 conflict trees), `check-no-conflict-markers-push`
  (20 files, 0 markers), `check-tree-size-push` (11 commits, 0 structural
  faults);
- `check-parser-source-global-ratchet.shs` PASS, and the range's three specs
  pass on the rebased base (21/21, 6/6, 5/5).

`--no-verify` nullifies the hook's other guards for that push. That is the cost,
it was accepted deliberately rather than by habit, and it is recorded here so
the next reader does not have to infer it. It does not discharge the debt above.

## Related

- `.claude/rules/vcs.md` § "Pre-push guards" — records that pushes here have
  routinely been made with `--no-verify`, which is how this class of debt
  accumulates unseen.
- `doc/05_design/platform/structural_compute/parser_sharing_contract_v1.md`
