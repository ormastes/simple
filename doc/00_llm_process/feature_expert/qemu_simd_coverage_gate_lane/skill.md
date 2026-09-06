# Feature Expert — QEMU SIMD and Coverage Gate Lane

## Role

Own process knowledge for the static-prerequisite tier of the QEMU SIMD lane
and the binary-independent half of the SIMD coverage lane. This is a lane about
**gate honesty**, not about SIMD kernels: the kernels were fine, the gate that
was supposed to prove it had never run to completion.

Scope is deliberately narrow. This lane does not own guest hit/chunk receipts,
QMP captures, the arch-matrix gate, `check-render2d-coverage.shs`, or any
RenderDoc/Electron/Chrome comparison. Those belong to
[simpleos_wm_qemu_evidence](../simpleos_wm_qemu_evidence/skill.md) and the
sosix QEMU matrix lane; do not edit their skills from here.

## Pipeline Links

- [research](../../skill_command/skills/pipe/research/skill.md)
- [design](../../skill_command/skills/pipe/design/skill.md)
- [impl](../../skill_command/skills/pipe/impl/skill.md)
- [verify](../../skill_command/skills/pipe/verify/skill.md)
- [release](../../skill_command/skills/pipe/release/skill.md)

## Feature Links

- Requirements owned: `REQ-QEMU-SIMD-COV-LANE-001` .. `-006` (defined in the
  spec docstring and the plan's traceability matrix; unique to this lane)
- Plan: `doc/03_plan/sys_test/qemu_simd_coverage_gate_lane.md`
- Executable spec: `test/03_system/check/qemu_simd_coverage_gate_lane_spec.spl`
- Authored mirror: `doc/06_spec/03_system/check/qemu_simd_coverage_gate_lane_spec.md`
- Guide: `doc/07_guide/platform/simpleos/qemu_system_tests.md`
  (§ QEMU SIMD Object Gate — Static Prerequisite Tier)
- SPipe state: `.spipe/qemu_simd_coverage_gate_lane/state.md`
- Gates owned:
  - `scripts/check/check-simpleos-qemu-engine2d-simd-kernels.shs`
  - `scripts/check/check-engine2d-simd-c-kernels.shs`
  - `scripts/check/check-x25519mlkem768-cpu-simd.shs`
  - `scripts/check/check-engine2d-simd-8k-ops.shs` (honesty flag only)

## Load-bearing facts

**1. The object gate had never passed (fixed `25dc443e44a`, 2026-08-16).**
Its ARM64 store assertion was `grep -Eq '[[:space:]]st1[[:space:]]+\\{'`. In
ERE a doubled backslash matches a literal backslash, so the pattern required a
backslash before the brace. llvm-objdump emits `st1` + tab + `{ v0.4s }, [x0]`
— no backslash. Measured on real disassembly: doubled form → **0** matches,
single form → **1** match.

**2. `set -eu` turns a failed assertion into a silent abort.** Because the
`grep -Eq` was the failing command, the script died with **exit 1 and zero
lines of stdout/stderr**, and the three assertions after it (`pshufd`,
`movdqu`, and the symbol loop) never ran. A silently-failing gate is
indistinguishable from a missing tool.

**3. Never read a gate's status through a pipe.** `sh gate.shs | tail` yields
`tail`'s status. This repo has produced false greens exactly this way, and it
is why the incident survived. Always:

```sh
sh scripts/check/<gate>.shs > gate.log 2>&1
rc=$?
```

**4. Origin had already fixed the sibling assertion, the shared worktree had
not.** `dup ... \.4s` was corrected upstream while `st1` was not, and the
shared `simple-main` working copy still held the *older* pre-fix version of the
whole script (hardcoded `objdump`, both over-escapes). Treat that worktree as
read-only evidence; forward deltas go on top of fetched `origin/main`.

**5. `engine2d-simd-8k-ops` passing is not an 80fps proof.** The gate requires
its own report to state `engine2d_8k_full_dynamic_frame_80fps_proven=false`.
A PASS from it means the receipt is well-formed and honest, nothing more.

**6. A reason in `guard_wiring_optout.txt` is a claim, not evidence.** Two of
this lane's four gates were justified there as needing "a real GPU or display,
unavailable on a general CI runner". Both were re-measured on a plain Linux
host with neither and both are GREEN. Corrected 2026-08-16 to state the real
reasons: a 7680x4320 x7-sample CPU benchmark is machine-dependent and slow as a
push gate, and the C-kernel gate is unwired by owner decision, not capability.
Before repeating any capability claim from that file, run the gate.

**7. No pure-Simple CLI is available in this environment, and bootstrapping
one is itself blocked.** `bin/simple` is the Rust seed (self-declared);
`bootstrap/stage3/simple` has no `test` command; `bootstrap-from-scratch.sh`
exits 64 needing a receipt only the pure-Simple planner can issue, and that
planner fails Stage 1 on a 180s native-build worker timeout. Consequence: the
arch-matrix and render2d-coverage gates cannot be run, and this lane's SSpec
cannot be executed or docgen'd. Record TEST_BLOCKED; never substitute the seed.

## How to work this lane

1. Run the four owned gates directly, reading `$?` on its own line.
2. If a gate is red, first check whether it is red *silently* — that is a gate
   defect, not necessarily a product defect. Trace with `sh -x`.
3. Fix the gate with the smallest possible diff; pin the regression in the
   system spec rather than in a new one-off script.
4. Record any claim the gate does not actually establish (see fact 5) instead
   of letting a PASS imply it.

## Anti-patterns

- Adding a skip path so an unqualified host reports green. Absence of a
  toolchain is absence of evidence.
- "Fixing" a red gate by relaxing its assertion instead of finding out whether
  the assertion was ever capable of matching.
- Citing this lane's SSpec as a passing result before an admitted pure-Simple
  CLI has executed it.
- Editing another pane's feature-expert skill or lane state to record findings
  that belong here.
