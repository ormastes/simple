# Simpleos String Replace Contract Specification

> Tests covering SimpleOS text.replace runtime parity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos String Replace Contract Specification

## Scenarios

### SimpleOS text.replace runtime parity

#### routes every baremetal architecture through replace-all semantics

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- routes every baremetal architecture through replace-all semantics


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("routes every baremetal architecture through replace-all semantics")
val x86 = file_read("examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c")
val x86_32 = file_read("examples/09_embedded/simple_os/arch/x86_32/boot/baremetal_stubs.c")
val arm_32 = file_read("examples/09_embedded/simple_os/arch/arm32/boot/baremetal_stubs.c")
val arm = file_read("examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c")
val rv = file_read("examples/09_embedded/simple_os/arch/riscv64/boot/baremetal_stubs.c")
val rv_ghdl = file_read("examples/09_embedded/simple_os/arch/riscv64/boot/ghdl_boot_info_runtime.c")

expect(replace_wrapper(x86)).to_contain("return rt_string_replace_all(str, old_val, new_val);")
expect(replace_wrapper(x86_32)).to_contain("return rt_string_replace_all(str, old_val, new_val);")
expect(replace_wrapper(arm_32)).to_contain("return rt_string_replace_all(str, old_val, new_val);")
expect(replace_wrapper(arm)).to_contain("return rt_string_replace_all(str, old_val, new_val);")
expect(replace_wrapper(rv)).to_contain("return rt_string_replace_all(str, old_val, new_val);")
expect(replace_wrapper(rv_ghdl)).to_contain("return rt_string_replace_all(str, old_val, new_val);")
expect(x86).to_contain("if (result_len_wide > (uint64_t)UINT32_MAX")
expect(x86_32).to_contain("if (result_len_wide > 0x100000U)")
expect(arm_32).to_contain("if (result_len_wide > 0x100000U)")
expect(arm).to_contain("if (result_len_wide > (uint64_t)UINT32_MAX")
expect(rv).to_contain("if (out_len_wide > (uint64_t)UINT32_MAX")
expect(rv_ghdl).to_contain("if (out_len_wide > (uint64_t)UINT32_MAX")
expect(x86_32).to_contain("if (len < 0 || len > 0x100000)")
expect(arm_32).to_contain("if (len < 0 || len > 0x100000)")
expect(x86_32).to_contain("if (sz > sizeof(_heap) - 15)")
expect(arm_32).to_contain("if (sz > sizeof(_heap) - 15)")
expect(x86_32).to_contain("if (_heap_off > sizeof(_heap) - sz)")
expect(arm_32).to_contain("if (_heap_off > sizeof(_heap) - sz)")

expect(replace_all_owner(x86)).to_contain("count++")
expect(replace_all_owner(x86_32)).to_contain("count++")
expect(replace_all_owner(arm_32)).to_contain("count++")
expect(replace_all_owner(arm)).to_contain("count++")
expect(replace_all_owner(rv)).to_contain("count++")
expect(replace_all_owner(rv_ghdl)).to_contain("count++")
expect(replace_all_owner(x86)).to_contain("o->len <= s->len - i")
expect(replace_all_owner(x86_32)).to_contain("o->len <= s->len - i")
expect(replace_all_owner(arm_32)).to_contain("o->len <= s->len - i")
expect(replace_all_owner(arm)).to_contain("o->len <= s->len - i")
expect(replace_all_owner(rv)).to_contain("o->len <= s->len - i")
expect(replace_all_owner(rv_ghdl)).to_contain("o->len <= s->len - i")
expect(replace_all_owner(rv)).to_contain("j < s->len - in")
expect(replace_all_owner(rv_ghdl)).to_contain("j < s->len - in")
```

</details>

#### keeps both RISC-V runtime algorithms identical

- keeps both RISC-V runtime algorithms identical
   - Expected: replace_all_owner(rv) equals `replace_all_owner(rv_ghdl)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("keeps both RISC-V runtime algorithms identical")
val rv = file_read("examples/09_embedded/simple_os/arch/riscv64/boot/baremetal_stubs.c")
val rv_ghdl = file_read("examples/09_embedded/simple_os/arch/riscv64/boot/ghdl_boot_info_runtime.c")

expect(replace_all_owner(rv)).to_equal(replace_all_owner(rv_ghdl))
```

</details>

#### compiles and executes the portable runtime behavior oracle

- compiles and executes the portable runtime behavior oracle
   - Expected: exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("compiles and executes the portable runtime behavior oracle")
val command = "out=/tmp/simpleos-string-replace-runtime-test.$$; trap 'rm -f \"$out\"' EXIT; cc -std=gnu11 -O0 -I. test/01_unit/os/port/simpleos_string_replace_runtime_test.c -o \"$out\" && \"$out\""
val (_stdout, _stderr, exit_code) = rt_process_run_timeout("/bin/sh", ["-c", command], 15000)

expect(exit_code).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/port/simpleos_string_replace_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS text.replace runtime parity.
- SimpleOS text.replace runtime parity

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

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `99e96c5d3b9e95a910f36209d3a510ba9500424609a17909a355fcfa69168418`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `99e96c5d3b9e95a910f36209d3a510ba9500424609a17909a355fcfa69168418`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `99e96c5d3b9e95a910f36209d3a510ba9500424609a17909a355fcfa69168418`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/os/port/simpleos_string_replace_contract_spec.spl
mirror: doc/06_spec/01_unit/os/port/simpleos_string_replace_contract_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/port/simpleos_string_replace_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/port/simpleos_string_replace_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/port/simpleos_string_replace_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/port/simpleos_string_replace_contract_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes every baremetal architecture through replace-all semantics' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/port/simpleos_string_replace_contract_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps both RISC-V runtime algorithms identical' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/port/simpleos_string_replace_contract_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles and executes the portable runtime behavior oracle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
