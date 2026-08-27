# MIR Native Code Generation

> Tests the MIR to native code generation path including register allocation, instruction selection, and machine code emission. Verifies that MIR instructions are correctly translated to platform-specific native instructions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MIR Native Code Generation

Tests the MIR to native code generation path including register allocation, instruction selection, and machine code emission. Verifies that MIR instructions are correctly translated to platform-specific native instructions.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | In Progress |
| Source | `test/03_system/feature/compiler/mir_native_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the MIR to native code generation path including register allocation,
instruction selection, and machine code emission. Verifies that MIR instructions
are correctly translated to platform-specific native instructions.

## Scenarios

### MIR Native

#### runs ISel on manually constructed MIR module

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- runs ISel on manually constructed MIR module
   - Expected: mach_module.functions.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runs ISel on manually constructed MIR module")
skip_on_interpreter "requires native backend":
    val module = build_hello_mir_module()
    val mach_module = isel_module(module)
    expect(mach_module.functions.len() > 0).to_equal(true)
```

</details>

#### produces non-empty ELF from MIR module

- produces non-empty ELF from MIR module
   - Expected: elf_bytes.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("produces non-empty ELF from MIR module")
skip_on_interpreter "requires native backend":
    val module = build_hello_mir_module()
    val mach_module = isel_module(module)
    val allocated = regalloc_module(mach_module)
    val encoded_funcs = encode_module(allocated)
    val elf_bytes = emit_elf(encoded_funcs, allocated)
    expect(elf_bytes.len() > 0).to_equal(true)
```

</details>

#### runs hello MIR binary and produces correct output

- runs hello MIR binary and produces correct output
   - Expected: link_r[2] equals `0`
   - Expected: run_r[0].trim() equals `hello from MIR!`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runs hello MIR binary and produces correct output")
skip_on_interpreter "requires native backend and linker":
    val module = build_hello_mir_module()
    val mach_module = isel_module(module)
    val allocated = regalloc_module(mach_module)
    val encoded_funcs = encode_module(allocated)
    val elf_bytes = emit_elf(encoded_funcs, allocated)

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
            shell("echo -n '{chunk}' > /tmp/mir_native_spec.hex")
        else:
            shell("echo -n '{chunk}' >> /tmp/mir_native_spec.hex")
        offset = end_idx

    shell("xxd -r -p /tmp/mir_native_spec.hex /tmp/mir_native_spec.o")
    shell("rm -f /tmp/mir_native_spec.hex")
    val link_r = rt_process_run("cc", ["-o", "/tmp/mir_native_spec", "/tmp/mir_native_spec.o", "-no-pie"])
    expect(link_r[2]).to_equal(0)

    val run_r = rt_process_run("/tmp/mir_native_spec", [])
    expect(run_r[0].trim()).to_equal("hello from MIR!")
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `83ce25767cf12c220a6b66498999980861e988b8f766fbf81b9f5015874d2a6f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `83ce25767cf12c220a6b66498999980861e988b8f766fbf81b9f5015874d2a6f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `83ce25767cf12c220a6b66498999980861e988b8f766fbf81b9f5015874d2a6f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/feature/compiler/mir_native_spec.spl
mirror: doc/06_spec/03_system/feature/compiler/mir_native_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/compiler/mir_native_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/compiler/mir_native_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/compiler/mir_native_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/compiler/mir_native_spec.spl:188:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs ISel on manually constructed MIR module' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/compiler/mir_native_spec.spl:196:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces non-empty ELF from MIR module' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/compiler/mir_native_spec.spl:207:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs hello MIR binary and produces correct output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
