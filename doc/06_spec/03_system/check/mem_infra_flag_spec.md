# `--mem-infra=` CLI Flag Wiring

> M3 wires `--mem-infra=a,b,c` (+ `--mem-infra-strict`) into the pure-Simple CLI for `simple run` (and `simple test`, transitively, since both dispatch through `main()` in `src/app/cli/_CliMain/main_and_help.spl`). The flag is parsed in `src/app/cli/_CliMain/args_and_os_commands.spl`, resolved against the capability matrix in `std.common.mem_infra.config` for the engine actually in use std.spec.step

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# `--mem-infra=` CLI Flag Wiring

M3 wires `--mem-infra=a,b,c` (+ `--mem-infra-strict`) into the pure-Simple CLI for `simple run` (and `simple test`, transitively, since both dispatch through `main()` in `src/app/cli/_CliMain/main_and_help.spl`). The flag is parsed in `src/app/cli/_CliMain/args_and_os_commands.spl`, resolved against the capability matrix in `std.common.mem_infra.config` for the engine actually in use std.spec.step

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Design | doc/03_plan/runtime/memory_analysis/memory_infra_next_phase_plan_2026-07-29.md M3 |
| Source | `test/03_system/check/mem_infra_flag_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

M3 wires `--mem-infra=a,b,c` (+ `--mem-infra-strict`) into the pure-Simple CLI
for `simple run` (and `simple test`, transitively, since both dispatch through
`main()` in `src/app/cli/_CliMain/main_and_help.spl`). The flag is parsed in
`src/app/cli/_CliMain/args_and_os_commands.spl`, resolved against the
capability matrix in `std.common.mem_infra.config` for the engine actually in
use std.spec.step

use (`cranelift` for a default run, `interpreter` when
`SIMPLE_EXECUTION_MODE=interpreter`), and applied via `env_set` before the
target program runs.

**Design:** doc/03_plan/runtime/memory_analysis/memory_infra_next_phase_plan_2026-07-29.md M3
**Library:** src/lib/common/mem_infra/config.spl

## Acceptance

- `--mem-infra=attr` on a default (cranelift) run enables `SIMPLE_MEM_ATTR=1`
  before the target program executes, observable via `rt_mem_attr_enabled()`.
- `--mem-infra=asan` on a default (cranelift) run — `asan` is llvm-only —
  degrades to `harden` with a `mem-infra: ... degraded to 'harden'` notice on
  stderr, and the run still exits 0.
- `--mem-infra=bogus` (unknown row) aborts before the program runs, with exit
  code 2.

## Scenarios

### --mem-infra= CLI flag

#### enables SIMPLE_MEM_ATTR before the target program runs on the default (cranelift) engine

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- enables SIMPLE_MEM_ATTR before the target program runs on the default (cranelift) engine
- Run the attr_enabled_probe fixture with --mem-infra=attr
- Confirm the child process exited cleanly and observed attribution enabled


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("enables SIMPLE_MEM_ATTR before the target program runs on the default (cranelift) engine")
step("Run the attr_enabled_probe fixture with --mem-infra=attr")
val (out, _err, code) = run_via_dispatch_probe(FIXTURE, ["--mem-infra=attr"])

step("Confirm the child process exited cleanly and observed attribution enabled")
assert_equal(code, 0)
expect(out).to_contain("enabled=1")
```

</details>

#### degrades an llvm-only row to its cranelift equivalent with a mem-infra notice, exit 0

- degrades an llvm-only row to its cranelift equivalent with a mem-infra notice, exit 0
- Run with --mem-infra=asan on the default (cranelift) engine
- Confirm a degrade notice was printed and the run still exits 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("degrades an llvm-only row to its cranelift equivalent with a mem-infra notice, exit 0")
step("Run with --mem-infra=asan on the default (cranelift) engine")
val (out, err, code) = run_via_dispatch_probe(FIXTURE, ["--mem-infra=asan"])
# The notice is written via eprint (stderr) in the normal deployed
# binary; combine with stdout so this assertion also holds under an
# interpreter/import topology where an eprint stub falls back to
# stdout (see doc/08_tracking/bug/ for the underlying mod_stub note).
val output = out + err

step("Confirm a degrade notice was printed and the run still exits 0")
expect(output).to_contain("mem-infra:")
expect(output).to_contain("degraded to 'harden'")
assert_equal(code, 0)
```

</details>

#### aborts with exit 2 on an unknown mem-infra row

- aborts with exit 2 on an unknown mem-infra row
- Run with --mem-infra=bogus
- Confirm the CLI reports the unknown row and aborts before running the program


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aborts with exit 2 on an unknown mem-infra row")
step("Run with --mem-infra=bogus")
val (out, err, code) = run_via_dispatch_probe(FIXTURE, ["--mem-infra=bogus"])
val output = out + err

step("Confirm the CLI reports the unknown row and aborts before running the program")
expect(output).to_contain("mem-infra:")
expect(output).to_contain("unknown mem-infra 'bogus'")
assert_equal(code, 2)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Design:** `doc/03_plan/runtime/memory_analysis/memory_infra_next_phase_plan_2026-07-29.md M3`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-MEM-INFRA-CLI-FLAG-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `144e7dab370b3e7e162af038e33a4d21a8c3d47ab3a91f8b78eafdd0f82fa68b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `144e7dab370b3e7e162af038e33a4d21a8c3d47ab3a91f8b78eafdd0f82fa68b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `144e7dab370b3e7e162af038e33a4d21a8c3d47ab3a91f8b78eafdd0f82fa68b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/check/mem_infra_flag_spec.spl
mirror: doc/06_spec/03_system/check/mem_infra_flag_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/03_system/check/mem_infra_flag_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/mem_infra_flag_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/mem_infra_flag_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/check/mem_infra_flag_spec.spl:143:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'enables SIMPLE_MEM_ATTR before the target program runs on the default (cranelift) engine' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/mem_infra_flag_spec.spl:153:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'degrades an llvm-only row to its cranelift equivalent with a mem-infra notice, exit 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/mem_infra_flag_spec.spl:169:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'aborts with exit 2 on an unknown mem-infra row' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
