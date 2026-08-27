# MIR Builder

> Tests the MIR (Mid-level Intermediate Representation) builder including instruction emission, basic block construction, and control flow graph generation. Verifies that HIR is correctly lowered to well-formed MIR with proper SSA properties.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MIR Builder

Tests the MIR (Mid-level Intermediate Representation) builder including instruction emission, basic block construction, and control flow graph generation. Verifies that HIR is correctly lowered to well-formed MIR with proper SSA properties.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | In Progress |
| Source | `test/03_system/feature/compiler/mir_builder_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the MIR (Mid-level Intermediate Representation) builder including instruction
emission, basic block construction, and control flow graph generation. Verifies
that HIR is correctly lowered to well-formed MIR with proper SSA properties.

## Scenarios

### MIR Builder

#### builds a function module with MirBuilder API

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- builds a function module with MirBuilder API
   - Expected: module.functions.keys().len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds a function module with MirBuilder API")
skip_on_interpreter "requires native backend":
    val module = build_30_module()
    expect(module.functions.keys().len()).to_equal(1)
```

</details>

#### compiles MirBuilder module and outputs '30'

- compiles MirBuilder module and outputs '30'
   - Expected: link_r[2] equals `0`
   - Expected: run_r[0].trim() equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles MirBuilder module and outputs '30'")
skip_on_interpreter "requires native backend and linker":
    val module = build_30_module()
    val mach_module = isel_module(module)
    val allocated = regalloc_module(mach_module)
    val encoded_funcs = encode_module(allocated)
    val elf_bytes = emit_elf_builder(encoded_funcs, allocated)

    var offset = 0
    while offset < elf_bytes.len():
        var chunk = ""
        var end_idx = offset + 800
        if end_idx > elf_bytes.len():
            end_idx = elf_bytes.len()
        var j = offset
        while j < end_idx:
            chunk = chunk + byte_to_hex(elf_bytes[j])
            j = j + 1
        if offset == 0:
            shell("echo -n '{chunk}' > /tmp/mir_builder_spec.hex")
        else:
            shell("echo -n '{chunk}' >> /tmp/mir_builder_spec.hex")
        offset = end_idx

    shell("xxd -r -p /tmp/mir_builder_spec.hex /tmp/mir_builder_spec.o")
    shell("rm -f /tmp/mir_builder_spec.hex")
    val link_r = rt_process_run("cc", ["-o", "/tmp/mir_builder_spec", "/tmp/mir_builder_spec.o", "-no-pie"])
    expect(link_r[2]).to_equal(0)

    val run_r = rt_process_run("/tmp/mir_builder_spec", [])
    expect(run_r[0].trim()).to_equal("30")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `810e448be10ac9a5c3989944fcca1fefd3f85c0d04c635d587c2a99ef24079a1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `810e448be10ac9a5c3989944fcca1fefd3f85c0d04c635d587c2a99ef24079a1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `810e448be10ac9a5c3989944fcca1fefd3f85c0d04c635d587c2a99ef24079a1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/feature/compiler/mir_builder_spec.spl
mirror: doc/06_spec/03_system/feature/compiler/mir_builder_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/compiler/mir_builder_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/compiler/mir_builder_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/compiler/mir_builder_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/compiler/mir_builder_spec.spl:199:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds a function module with MirBuilder API' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/compiler/mir_builder_spec.spl:206:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles MirBuilder module and outputs '30'' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
