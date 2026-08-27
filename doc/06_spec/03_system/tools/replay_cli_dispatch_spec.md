# Replay Cli Dispatch Specification

> Tests covering qemu subcommand parse_flag.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Cli Dispatch Specification

## Scenarios

### qemu subcommand parse_flag

#### parse_flag extracts --arch value

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parse_flag extracts --arch value
   - Expected: v equals `x86_64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parse_flag extracts --arch value")
val a = ["--arch", "x86_64", "--kernel", "boot.elf"]
val v = parse_flag(a, "--arch")
expect(v).to_equal("x86_64")
```

</details>

#### parse_flag extracts --kernel value

- parse_flag extracts --kernel value
   - Expected: v equals `boot.elf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parse_flag extracts --kernel value")
val a = ["--arch", "riscv32", "--kernel", "boot.elf", "--trace", "out.srrq"]
val v = parse_flag(a, "--kernel")
expect(v).to_equal("boot.elf")
```

</details>

#### parse_flag extracts --trace value

- parse_flag extracts --trace value
   - Expected: v equals `recording.srrq`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parse_flag extracts --trace value")
val a = ["--arch", "x86_64", "--kernel", "boot.elf", "--trace", "recording.srrq"]
val v = parse_flag(a, "--trace")
expect(v).to_equal("recording.srrq")
```

</details>

#### parse_flag extracts --gdb-port value

- parse_flag extracts --gdb-port value
   - Expected: v equals `5555`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parse_flag extracts --gdb-port value")
val a = ["--kernel", "boot.elf", "--trace", "rec.srrq", "--gdb-port", "5555"]
val v = parse_flag(a, "--gdb-port")
expect(v).to_equal("5555")
```

</details>

#### parse_flag returns empty text for missing flag

- parse_flag returns empty text for missing flag
   - Expected: v equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parse_flag returns empty text for missing flag")
val a = ["--arch", "x86_64"]
val v = parse_flag(a, "--kernel")
expect(v).to_equal("")
```

</details>

#### parse_flag returns empty for unrelated args

- parse_flag returns empty for unrelated args
   - Expected: v equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parse_flag returns empty for unrelated args")
val a = ["--unrelated", "value"]
val v = parse_flag(a, "--arch")
expect(v).to_equal("")
```

</details>

#### parse_flag extracts --qmp socket path

- parse_flag extracts --qmp socket path
   - Expected: v equals `/tmp/qemu-qmp.sock`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parse_flag extracts --qmp socket path")
val a = ["save", "snap1", "--qmp", "/tmp/qemu-qmp.sock"]
val v = parse_flag(a, "--qmp")
expect(v).to_equal("/tmp/qemu-qmp.sock")
```

</details>

#### parse_flag extracts --machine value

- parse_flag extracts --machine value
   - Expected: v equals `virt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parse_flag extracts --machine value")
val a = ["--arch", "aarch64", "--kernel", "k.elf", "--machine", "virt"]
val v = parse_flag(a, "--machine")
expect(v).to_equal("virt")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/replay_cli_dispatch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering qemu subcommand parse_flag.
- qemu subcommand parse_flag

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `68cf0901d325cd572f6fd73b0a4ed718b58d10b916a9284069cdc957d3efbb75`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `68cf0901d325cd572f6fd73b0a4ed718b58d10b916a9284069cdc957d3efbb75`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `68cf0901d325cd572f6fd73b0a4ed718b58d10b916a9284069cdc957d3efbb75`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/replay_cli_dispatch_spec.spl
mirror: doc/06_spec/03_system/tools/replay_cli_dispatch_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/replay_cli_dispatch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/replay_cli_dispatch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/replay_cli_dispatch_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parse_flag extracts --arch value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/replay_cli_dispatch_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parse_flag extracts --kernel value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/replay_cli_dispatch_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parse_flag extracts --trace value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
