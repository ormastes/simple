# SimpleOS mission-critical release blocked by missing SymbiYosys stack

- **Date:** 2026-07-05
- **Severity:** P1 (release evidence — mission-critical SimpleOS release cannot
  pass strict RTL proof gate)
- **Repro:** run `sh scripts/check/check-simpleos-mission-critical-prereqs.shs`
  on this host.

## Observed

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

## Next Action

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
