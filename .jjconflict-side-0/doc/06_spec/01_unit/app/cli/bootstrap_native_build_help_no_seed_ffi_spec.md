# Bootstrap Native Build Help No Seed Ffi Specification

> Tests covering bootstrap native-build help.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bootstrap Native Build Help No Seed Ffi Specification

## Scenarios

### bootstrap native-build help

#### answers --help in-process instead of calling the seed extern

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- answers --help in-process instead of calling the seed extern
   - Expected: source does not contain `if removed_bundle == "--help" or removed_bundle == "-h" or removed_bundle == ... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("answers --help in-process instead of calling the seed extern")
val source = bootstrap_main_source()

expect(source).to_contain("if removed_bundle == \"--help\" or removed_bundle == \"-h\":")
expect(source).to_contain("print \"Usage: simple native-build <file>.spl [-o <output>] [--backend=<llvm|cranelift>]\"")
# The pre-fix line bundled --help with --list-optimizations and sent all
# three into the seed FFI. It must be gone.
expect(source.contains("if removed_bundle == \"--help\" or removed_bundle == \"-h\" or removed_bundle == \"--list-optimizations\":")).to_equal(false)
```

</details>

#### rejects a bare native-build with no source instead of crashing

- rejects a bare native-build with no source instead of crashing


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects a bare native-build with no source instead of crashing")
val source = bootstrap_main_source()

expect(source).to_contain("if args.len() < 3:")
expect(source).to_contain("print \"error: missing source file\"")
```

</details>

#### keeps the seed extern reachable only for the real build lanes

- keeps the seed extern reachable only for the real build lanes


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps the seed extern reachable only for the real build lanes")
val source = bootstrap_main_source()

# --list-optimizations still needs the seed's optimization registry; it
# is knowingly left on the FFI route (tracked in the bug record).
expect(source).to_contain("if removed_bundle == \"--list-optimizations\":")
expect(source).to_contain("extern fn rt_native_build(args: [text]) -> i64")
```

</details>

#### documents why native_build_help cannot hold the text

- documents why native_build_help cannot hold the text


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("documents why native_build_help cannot hold the text")
val source = bootstrap_main_source()
val lowering = rt_file_read_text("src/compiler/50.mir/_MirLowering/module_lowering.spl") ?? ""

# native_build_help()'s BODY is hardcoded in bootstrap MIR lowering, so
# editing its .spl source would be silently ignored in the capsule.
expect(lowering).to_contain("if name == \"native_build_help\":")
expect(source).to_contain("hardcoded")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli/bootstrap_native_build_help_no_seed_ffi_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering bootstrap native-build help.
- bootstrap native-build help

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4dcecc5a8117519f87ac03b71c67f00a9548a5c9a7292dd2326bcdcd6e5ee122`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4dcecc5a8117519f87ac03b71c67f00a9548a5c9a7292dd2326bcdcd6e5ee122`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4dcecc5a8117519f87ac03b71c67f00a9548a5c9a7292dd2326bcdcd6e5ee122`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/app/cli/bootstrap_native_build_help_no_seed_ffi_spec.spl
mirror: doc/06_spec/01_unit/app/cli/bootstrap_native_build_help_no_seed_ffi_spec.md (current)
findings: 7 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/01_unit/app/cli/bootstrap_native_build_help_no_seed_ffi_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/cli/bootstrap_native_build_help_no_seed_ffi_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/cli/bootstrap_native_build_help_no_seed_ffi_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/app/cli/bootstrap_native_build_help_no_seed_ffi_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/cli/bootstrap_native_build_help_no_seed_ffi_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'answers --help in-process instead of calling the seed extern' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/cli/bootstrap_native_build_help_no_seed_ffi_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a bare native-build with no source instead of crashing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/cli/bootstrap_native_build_help_no_seed_ffi_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the seed extern reachable only for the real build lanes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
