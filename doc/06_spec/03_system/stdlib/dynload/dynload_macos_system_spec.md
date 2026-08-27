# TODO(dynload-system-tests): switch to gcc -shared + file_read_bytes

> macOS Dynamic Loading System Test.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# TODO(dynload-system-tests): switch to gcc -shared + file_read_bytes

macOS Dynamic Loading System Test.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #DYNLOAD-SYS-011 to #DYNLOAD-SYS-012 |
| Category | Infrastructure / System Test |
| Status | Active |
| Source | `test/03_system/stdlib/dynload/dynload_macos_system_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

macOS Dynamic Loading System Test.

Exercises the dylib_registry ELF cross-load pipeline on macOS. Since
no Mach-O loader exists, this verifies that the ELF registry works
cross-platform. Gated by is_macos() -- prints SKIP on other platforms.

## Scenarios

### Dynload macOS System

### ELF cross-load via registry

#### registers and resolves ELF64 on macOS

- registers and resolves ELF64 on macOS
   - Expected: dylib_registry_symbol(handle, "_start") equals `0x400000`
   - Expected: dylib_registry_close(handle) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("registers and resolves ELF64 on macOS")
if is_macos():
    dylib_registry_reset_for_test()
    val handle = dylib_registry_register("/lib/cross.so", make_elf64_exec())
    expect(handle).to_be_greater_than(0)
    expect(dylib_registry_symbol(handle, "_start")).to_equal(0x400000)
    expect(dylib_registry_close(handle)).to_equal(0)
    dylib_registry_reset_for_test()
else:
    print("SKIP: macOS ELF cross-load (not on macOS)")
```

</details>

#### resolves main entry symbol on macOS

- resolves main entry symbol on macOS
   - Expected: dylib_registry_symbol(handle, "main") equals `0x400000`
   - Expected: dylib_registry_close(handle) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("resolves main entry symbol on macOS")
if is_macos():
    dylib_registry_reset_for_test()
    val handle = dylib_registry_register("/lib/mac.so", make_elf64_exec())
    expect(handle).to_be_greater_than(0)
    expect(dylib_registry_symbol(handle, "main")).to_equal(0x400000)
    expect(dylib_registry_close(handle)).to_equal(0)
    dylib_registry_reset_for_test()
else:
    print("SKIP: macOS symbol resolve (not on macOS)")
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

- Canonical SPipe generation for source `28eac42eeabdf6f97ac6eb23ab211fadc1e9578f62812ef5b6905b6a3dbf45fa`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `28eac42eeabdf6f97ac6eb23ab211fadc1e9578f62812ef5b6905b6a3dbf45fa`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `28eac42eeabdf6f97ac6eb23ab211fadc1e9578f62812ef5b6905b6a3dbf45fa`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/stdlib/dynload/dynload_macos_system_spec.spl
mirror: doc/06_spec/03_system/stdlib/dynload/dynload_macos_system_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/stdlib/dynload/dynload_macos_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/stdlib/dynload/dynload_macos_system_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/stdlib/dynload/dynload_macos_system_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/stdlib/dynload/dynload_macos_system_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'registers and resolves ELF64 on macOS' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/stdlib/dynload/dynload_macos_system_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves main entry symbol on macOS' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
