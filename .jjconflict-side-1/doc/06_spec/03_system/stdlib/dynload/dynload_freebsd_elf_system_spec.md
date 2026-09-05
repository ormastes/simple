# dynload_freebsd_elf_system_spec

> FreeBSD Dynamic Loading System Test.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# dynload_freebsd_elf_system_spec

FreeBSD Dynamic Loading System Test.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/stdlib/dynload/dynload_freebsd_elf_system_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

FreeBSD Dynamic Loading System Test.

Pins the platform-independent ELF registry contract on every host and retains
a native FreeBSD witness for the QEMU/bootstrap lane.

## Scenarios

### Dynload FreeBSD ELF System

#### registers resolves retains and closes the FreeBSD ELF contract

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- registers resolves retains and closes the FreeBSD ELF contract
   - Expected: dylib_registry_symbol(handle, "_start") equals `0x400000`
   - Expected: dylib_registry_open("/usr/local/lib/libsimple.so") equals `handle`
   - Expected: dylib_registry_close(handle) equals `0`
   - Expected: dylib_registry_symbol(handle, "main") equals `0x400000`
   - Expected: dylib_registry_close(handle) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("registers resolves retains and closes the FreeBSD ELF contract")
dylib_registry_reset_for_test()
val handle = dylib_registry_register("/usr/local/lib/libsimple.so", make_elf64_exec())
expect(handle).to_be_greater_than(0)
expect(dylib_registry_symbol(handle, "_start")).to_equal(0x400000)
expect(dylib_registry_open("/usr/local/lib/libsimple.so")).to_equal(handle)
expect(dylib_registry_close(handle)).to_equal(0)
expect(dylib_registry_symbol(handle, "main")).to_equal(0x400000)
expect(dylib_registry_close(handle)).to_equal(0)
expect(dylib_registry_symbol(handle, "main")).to_be_less_than(0)
dylib_registry_reset_for_test()
```

</details>

#### provides a native FreeBSD host witness when running on FreeBSD

- provides a native FreeBSD host witness when running on FreeBSD
   - Expected: dylib_registry_symbol(handle, "main") equals `0x400000`
   - Expected: dylib_registry_close(handle) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("provides a native FreeBSD host witness when running on FreeBSD")
if detect_os() == "freebsd":
    dylib_registry_reset_for_test()
    val handle = dylib_registry_register("/usr/lib/libsimple_native.so", make_elf64_exec())
    expect(handle).to_be_greater_than(0)
    expect(dylib_registry_symbol(handle, "main")).to_equal(0x400000)
    expect(dylib_registry_close(handle)).to_equal(0)
    dylib_registry_reset_for_test()
else:
    print("SKIP: native FreeBSD loader witness (not on FreeBSD)")
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

- Canonical SPipe generation for source `547fb0257093f4c5a069a67db87db271e35153e6ccf7592a135b6f6cf00ea9e7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `547fb0257093f4c5a069a67db87db271e35153e6ccf7592a135b6f6cf00ea9e7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `547fb0257093f4c5a069a67db87db271e35153e6ccf7592a135b6f6cf00ea9e7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/stdlib/dynload/dynload_freebsd_elf_system_spec.spl
mirror: doc/06_spec/03_system/stdlib/dynload/dynload_freebsd_elf_system_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/stdlib/dynload/dynload_freebsd_elf_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/stdlib/dynload/dynload_freebsd_elf_system_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/stdlib/dynload/dynload_freebsd_elf_system_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/stdlib/dynload/dynload_freebsd_elf_system_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'registers resolves retains and closes the FreeBSD ELF contract' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/stdlib/dynload/dynload_freebsd_elf_system_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'provides a native FreeBSD host witness when running on FreeBSD' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
