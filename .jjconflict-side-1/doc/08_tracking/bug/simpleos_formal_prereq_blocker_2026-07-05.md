# SimpleOS mission-critical formal prereq blocker

- **Date:** 2026-07-05
- **Status:** Closed 2026-07-05
- **Severity:** Was P1 (release evidence — mission-critical SimpleOS release
  could not pass the strict RTL proof gate until formal tools were available)
- **Closing evidence:** OSS CAD Suite is available at
  `/tmp/simple-oss-cad-suite/oss-cad-suite`; with its `environment` sourced,
  prereqs, strict RTL/SBY proof, the hardening matrix, and the
  mission-critical release wrapper all pass.

## Observed

Current evidence:

```text
simpleos_mission_critical_prereqs_status=ready
simpleos_mission_critical_prereqs_missing=none
STATUS: PASS riscv-rtl-sby-proof
simpleos_hardening_matrix_status=pass
simpleos_hardening_matrix_passed=26/26
simpleos_hardening_riscv_rtl_sby_proof_status=pass
STATUS: PASS simpleos-mission-critical-release matrix_status=pass release_status=pass release_blockers=none prereq_status=ready prereq_missing=none prereq_next_action=none
```

Previous blocked observation:

The prereq gate reports:

```text
simpleos_mission_critical_prereqs_status=blocked
simpleos_mission_critical_prereqs_missing=sby,yosys,smt-solver
```

No `sby`, `yosys`, `boolector`, `z3`, `nix`, `conda`, `micromamba`, or local
OSS CAD Suite path was found. `sudo -n true` reports that sudo needs a password,
so this session cannot use the documented apt path.

## Expected

The host used for mission-critical release evidence has `sby`, `yosys`, and at
least one supported SMT solver such as `boolector` or `z3` available on `PATH`.

## Reopen If

Reopen only if a fresh mission-critical release host cannot source OSS CAD
Suite or otherwise provide `sby`, `yosys`, and one SMT solver, and
`scripts/check/check-simpleos-mission-critical-release.shs` returns nonzero.

## Historical Setup Action

Run:

```bash
sh scripts/setup/setup-simpleos-formal-env.shs --print-install
sudo apt-get update
sudo apt-get install yosys symbiyosys boolector z3
sh scripts/check/check-simpleos-mission-critical-prereqs.shs
sh scripts/check/check-simpleos-mission-critical-release.shs
```

No-sudo alternative:

1. Download the free OSS CAD Suite release from
   <https://github.com/YosysHQ/oss-cad-suite-build/releases>.
2. Extract it under a user-writable directory.
3. Source its environment:

```bash
. /path/to/oss-cad-suite/environment
command -v sby yosys
command -v boolector || command -v z3
sh scripts/check/check-simpleos-mission-critical-prereqs.shs
sh scripts/check/check-simpleos-mission-critical-release.shs
```
