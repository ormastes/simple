# clang_static_e2e_spec

> Live fail-closed QEMU proof. The Clang ELF must be read from FAT32, emit a

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# clang_static_e2e_spec

Live fail-closed QEMU proof. The Clang ELF must be read from FAT32, emit a

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/system/os/port/clang_static_e2e_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

Live fail-closed QEMU proof. The Clang ELF must be read from FAT32, emit a
    real object, link hello.elf in-guest, then load that filesystem ELF in ring
    3 and independently report its output.

## Scenarios

### Clang compiles links and executes from the SimpleOS filesystem

#### runs Clang from FAT32 through guest object link and execution

- runs Clang from FAT32 through guest object link and execution
- Require SIMPLEOS_CLANG_FS_E2E=1
   - Expected: env_get("SIMPLEOS_CLANG_FS_E2E") equals `1`
- Require the guest-native Clang payload and QEMU wrapper
- Run the Clang filesystem QEMU wrapper
   - Expected: exit_code equals `0`
- Require hashed kernel and filesystem artifacts
- Require a guest-produced x86-64 ELF object
- Require in-guest linking of the hello executable
- Require filesystem loading and independent hello execution


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runs Clang from FAT32 through guest object link and execution")
step("Require SIMPLEOS_CLANG_FS_E2E=1")
expect(env_get("SIMPLEOS_CLANG_FS_E2E")).to_equal("1")
step("Require the guest-native Clang payload and QEMU wrapper")
expect(file_exists(CLANG_GUEST_BINARY)).to_be(true)
expect(file_exists(CLANG_DISK_SCRIPT)).to_be(true)

step("Run the Clang filesystem QEMU wrapper")
val (stdout, stderr, exit_code) = process_run("/bin/sh", [CLANG_DISK_SCRIPT])
val output = stdout + stderr
expect(exit_code).to_equal(0)

step("Require hashed kernel and filesystem artifacts")
expect(output).to_contain("[clang-disk] artifact kernel=")
expect(output).to_contain("sha256=")
expect(output).to_contain("[clang-disk] artifact image=")

step("Require a guest-produced x86-64 ELF object")
expect(output).to_contain("[clang-disk] PASS guest_exit=0")
expect(output).to_contain("format=ELF64 type=REL machine=x86-64 symbol=main")

step("Require in-guest linking of the hello executable")
expect(output).to_contain("[clang-disk] PASS guest_link=/hello.elf")

step("Require filesystem loading and independent hello execution")
expect(output).to_contain("hello-from-simpleos-clang")
expect(output).to_contain("[syscall] exit status=42")
expect(output).to_contain("[prod-ring3] PASS filesystem Simple ELF executed")
expect(output).to_contain("[clang-disk] PASS guest_exec=/hello.elf output=hello-from-simpleos-clang")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
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

- Canonical SPipe generation for source `b50370ae180e0aababd0e44fbfe724dc1ffc17512116ddd3ef6af855ac244a24`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b50370ae180e0aababd0e44fbfe724dc1ffc17512116ddd3ef6af855ac244a24`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b50370ae180e0aababd0e44fbfe724dc1ffc17512116ddd3ef6af855ac244a24`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **93/100**; effective score: **93/100**; blockers: **0**.

SSpec documentization score: 93/100
source: test/system/os/port/clang_static_e2e_spec.spl
mirror: doc/06_spec/system/os/port/clang_static_e2e_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/system/os/port/clang_static_e2e_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/system/os/port/clang_static_e2e_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/system/os/port/clang_static_e2e_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/system/os/port/clang_static_e2e_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs Clang from FAT32 through guest object link and execution' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
