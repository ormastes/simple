# arch_common_wave3_sbi_dedupe_spec

> Verifies the arch common wave3 sbi dedupe behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# arch_common_wave3_sbi_dedupe_spec

Verifies the arch common wave3 sbi dedupe behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/multiarch/arch_common_wave3_sbi_dedupe_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the arch common wave3 sbi dedupe behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### sbi_shim — SBI extension IDs come from the specification, not per-arch copies

#### states the SBI extension IDs at their specified values

- Verify: states the SBI extension IDs at their specified values
- read the extension IDs from the shared shim
   - Expected: SBI_EXT_BASE equals `0x10`
   - Expected: SBI_EXT_TIMER equals `0x54494D45`
   - Expected: SBI_EXT_IPI equals `0x735049`
   - Expected: SBI_EXT_HSM equals `0x48534D`
   - Expected: SBI_EXT_SRST equals `0x53525354`
   - Expected: SBI_EXT_RFENCE equals `0x52464E43`
   - Expected: SBI_EXT_DBCN equals `0x4442434E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-ARCH-COMMON-SBI-002 REQ-OS-ARCH-COMMON-SBI-003 REQ-OS-ARCH-COMMON-SBI-004 REQ-OS-ARCH-COMMON-SBI-005 REQ-OS-ARCH-COMMON-SBI-006 REQ-OS-ARCH-COMMON-SBI-007
step("Verify: states the SBI extension IDs at their specified values")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("read the extension IDs from the shared shim")
expect(SBI_EXT_BASE).to_equal(0x10)
expect(SBI_EXT_TIMER).to_equal(0x54494D45)
expect(SBI_EXT_IPI).to_equal(0x735049)
expect(SBI_EXT_HSM).to_equal(0x48534D)
expect(SBI_EXT_SRST).to_equal(0x53525354)
expect(SBI_EXT_RFENCE).to_equal(0x52464E43)
expect(SBI_EXT_DBCN).to_equal(0x4442434E)
```

</details>

#### states the legacy extension IDs the boot console and shutdown paths use

- Verify: states the legacy extension IDs the boot console and shutdown paths use
- read the four legacy extension IDs
   - Expected: SBI_EXT_LEGACY_CONSOLE_PUTCHAR equals `0x01`
   - Expected: SBI_EXT_LEGACY_CONSOLE_GETCHAR equals `0x02`
   - Expected: SBI_EXT_LEGACY_SEND_IPI equals `0x04`
   - Expected: SBI_EXT_LEGACY_SHUTDOWN equals `0x08`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-ARCH-COMMON-SBI-001 REQ-OS-ARCH-COMMON-SBI-003 REQ-OS-ARCH-COMMON-SBI-004 REQ-OS-ARCH-COMMON-SBI-005 REQ-OS-ARCH-COMMON-SBI-006 REQ-OS-ARCH-COMMON-SBI-007
step("Verify: states the legacy extension IDs the boot console and shutdown paths use")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("read the four legacy extension IDs")
expect(SBI_EXT_LEGACY_CONSOLE_PUTCHAR).to_equal(0x01)
expect(SBI_EXT_LEGACY_CONSOLE_GETCHAR).to_equal(0x02)
expect(SBI_EXT_LEGACY_SEND_IPI).to_equal(0x04)
expect(SBI_EXT_LEGACY_SHUTDOWN).to_equal(0x08)
```

</details>

#### states the standard SBI error codes as signed values

- Verify: states the standard SBI error codes as signed values
- read the error envelope from the shared shim
   - Expected: SBI_OK equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: SBI_ERR_FAILED equals `-1)  # oracle: pinned constant asserted by this scenario`
   - Expected: SBI_ERR_NOT_SUPPORTED equals `-2)  # oracle: pinned constant asserted by this scenario`
   - Expected: SBI_ERR_INVALID_PARAM equals `-3)  # oracle: pinned constant asserted by this scenario`
   - Expected: SBI_ERR_DENIED equals `-4)  # oracle: pinned constant asserted by this scenario`
   - Expected: SBI_ERR_INVALID_ADDRESS equals `-5)  # oracle: pinned constant asserted by this scenario`
   - Expected: SBI_ERR_ALREADY_AVAILABLE equals `-6)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-ARCH-COMMON-SBI-001 REQ-OS-ARCH-COMMON-SBI-003 REQ-OS-ARCH-COMMON-SBI-004 REQ-OS-ARCH-COMMON-SBI-005 REQ-OS-ARCH-COMMON-SBI-006 REQ-OS-ARCH-COMMON-SBI-007
step("Verify: states the standard SBI error codes as signed values")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("read the error envelope from the shared shim")
expect(SBI_OK).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(SBI_ERR_FAILED).to_equal(-1)  # oracle: pinned constant asserted by this scenario
expect(SBI_ERR_NOT_SUPPORTED).to_equal(-2)  # oracle: pinned constant asserted by this scenario
expect(SBI_ERR_INVALID_PARAM).to_equal(-3)  # oracle: pinned constant asserted by this scenario
expect(SBI_ERR_DENIED).to_equal(-4)  # oracle: pinned constant asserted by this scenario
expect(SBI_ERR_INVALID_ADDRESS).to_equal(-5)  # oracle: pinned constant asserted by this scenario
expect(SBI_ERR_ALREADY_AVAILABLE).to_equal(-6)  # oracle: pinned constant asserted by this scenario
```

</details>

#### treats only error code zero as success

- Verify: treats only error code zero as success
- ask the shim whether each error code means success


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-ARCH-COMMON-SBI-001 REQ-OS-ARCH-COMMON-SBI-002 REQ-OS-ARCH-COMMON-SBI-004 REQ-OS-ARCH-COMMON-SBI-005 REQ-OS-ARCH-COMMON-SBI-006 REQ-OS-ARCH-COMMON-SBI-007
step("Verify: treats only error code zero as success")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("ask the shim whether each error code means success")
expect(sbi_ok(SbiResult(err: SBI_OK, value: 0))).to_be_true()
expect(sbi_ok(SbiResult(err: SBI_ERR_NOT_SUPPORTED, value: 0))).to_be_false()
```

</details>

#### packages a probe request as the base extension plus the queried ID

- Verify: packages a probe request as the base extension plus the queried ID
- build the probe argument pair for the timer extension
   - Expected: args[0] equals `SBI_EXT_BASE`
   - Expected: args[1] equals `SBI_EXT_TIMER`
   - Expected: SBI_BASE_PROBE_EXTENSION equals `3)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-ARCH-COMMON-SBI-001 REQ-OS-ARCH-COMMON-SBI-002 REQ-OS-ARCH-COMMON-SBI-003 REQ-OS-ARCH-COMMON-SBI-004 REQ-OS-ARCH-COMMON-SBI-005 REQ-OS-ARCH-COMMON-SBI-006 REQ-OS-ARCH-COMMON-SBI-007
step("Verify: packages a probe request as the base extension plus the queried ID")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("build the probe argument pair for the timer extension")
val args = sbi_probe_request_args(SBI_EXT_TIMER)
expect(args[0]).to_equal(SBI_EXT_BASE)
expect(args[1]).to_equal(SBI_EXT_TIMER)
expect(SBI_BASE_PROBE_EXTENSION).to_equal(3)  # oracle: pinned constant asserted by this scenario
```

</details>

### riscv64 forwards to the shim instead of redeclaring

#### imports the shared shim

- Verify: imports the shared shim
- read the rv64 SBI source


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-ARCH-COMMON-SBI-001 REQ-OS-ARCH-COMMON-SBI-002 REQ-OS-ARCH-COMMON-SBI-003 REQ-OS-ARCH-COMMON-SBI-005 REQ-OS-ARCH-COMMON-SBI-006 REQ-OS-ARCH-COMMON-SBI-007
step("Verify: imports the shared shim")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("read the rv64 SBI source")
val body = file_read(RV64_SBI)
expect(body).to_contain("use os.kernel.arch.common.sbi_shim.{")
```

</details>

#### leaves no local redeclaration of any forwarded constant

- Verify: leaves no local redeclaration of any forwarded constant
- scan rv64 for `val <NAME>:` redeclarations
   - Expected: copies equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-ARCH-COMMON-SBI-001 REQ-OS-ARCH-COMMON-SBI-002 REQ-OS-ARCH-COMMON-SBI-003 REQ-OS-ARCH-COMMON-SBI-004 REQ-OS-ARCH-COMMON-SBI-006 REQ-OS-ARCH-COMMON-SBI-007
step("Verify: leaves no local redeclaration of any forwarded constant")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("scan rv64 for `val <NAME>:` redeclarations")
val body = file_read(RV64_SBI)
var copies = 0
for n in RV64_FORWARDED:
    if body.contains("val " + n + ":"):
        copies = copies + 1
expect(copies).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### keeps the ecall trampoline in the arch file, not the shim

- Verify: keeps the ecall trampoline in the arch file, not the shim
- confirm the register-level trampoline stayed per-arch


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-ARCH-COMMON-SBI-001 REQ-OS-ARCH-COMMON-SBI-002 REQ-OS-ARCH-COMMON-SBI-003 REQ-OS-ARCH-COMMON-SBI-004 REQ-OS-ARCH-COMMON-SBI-006 REQ-OS-ARCH-COMMON-SBI-007
step("Verify: keeps the ecall trampoline in the arch file, not the shim")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("confirm the register-level trampoline stayed per-arch")
val body = file_read(RV64_SBI)
expect(body).to_contain("fn sbi_call(")
val shim = file_read(COMMON_SBI)
expect(shim.contains("fn sbi_call(")).to_be_false()
expect(shim.contains("extern fn")).to_be_false()
```

</details>

#### keeps its own historical spelling of the reset extension as an alias

- Verify: keeps its own historical spelling of the reset extension as an alias
- confirm SBI_EXT_SYSTEM_RESET is derived, not a fresh literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-ARCH-COMMON-SBI-001 REQ-OS-ARCH-COMMON-SBI-002 REQ-OS-ARCH-COMMON-SBI-003 REQ-OS-ARCH-COMMON-SBI-004 REQ-OS-ARCH-COMMON-SBI-005 REQ-OS-ARCH-COMMON-SBI-006 REQ-OS-ARCH-COMMON-SBI-007
step("Verify: keeps its own historical spelling of the reset extension as an alias")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("confirm SBI_EXT_SYSTEM_RESET is derived, not a fresh literal")
val body = file_read(RV64_SBI)
expect(body).to_contain("val SBI_EXT_SYSTEM_RESET: u64 = SBI_EXT_SRST")
expect(body).to_contain("val SBI_SUCCESS: i64 = SBI_OK")
```

</details>

### riscv32 stays u32-typed but must not drift in value

#### declares the same extension ID numbers the shim states

- Verify: declares the same extension ID numbers the shim states
- read the rv32 SBI source and compare each shared ID


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-ARCH-COMMON-SBI-001 REQ-OS-ARCH-COMMON-SBI-002 REQ-OS-ARCH-COMMON-SBI-003 REQ-OS-ARCH-COMMON-SBI-004 REQ-OS-ARCH-COMMON-SBI-005 REQ-OS-ARCH-COMMON-SBI-006
step("Verify: declares the same extension ID numbers the shim states")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("read the rv32 SBI source and compare each shared ID")
val body = file_read(RV32_SBI)
expect(body).to_contain("val SBI_EXT_TIMER: u32 = 0x54494D45")
expect(body).to_contain("val SBI_EXT_HSM: u32 = 0x48534D")
expect(body).to_contain("val SBI_EXT_SRST: u32 = 0x53525354")
expect(body).to_contain("val SBI_EXT_PUTCHAR: u32 = 0x01")
expect(body).to_contain("val SBI_EXT_GETCHAR: u32 = 0x02")
expect(body).to_contain("val SBI_EXT_SHUTDOWN: u32 = 0x08")
```

</details>

#### pins the fourth live copy of the IPI extension ID in rv32 hal_smp

- Verify: pins the fourth live copy of the IPI extension ID in rv32 hal_smp
- read rv32 hal_smp, which carries its own u32 IPI ext ID
   - Expected: SBI_EXT_IPI equals `0x735049`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-ARCH-COMMON-SBI-001 REQ-OS-ARCH-COMMON-SBI-002 REQ-OS-ARCH-COMMON-SBI-003 REQ-OS-ARCH-COMMON-SBI-004 REQ-OS-ARCH-COMMON-SBI-005 REQ-OS-ARCH-COMMON-SBI-007
step("Verify: pins the fourth live copy of the IPI extension ID in rv32 hal_smp")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("read rv32 hal_smp, which carries its own u32 IPI ext ID")
val smp = file_read("src/os/kernel/arch/riscv32/hal_smp.spl")
expect(smp).to_contain("val SBI_EXT_IPI_RV32: u32 = 0x735049u32")
expect(SBI_EXT_IPI).to_equal(0x735049)
```

</details>

#### records why rv32 was not converted to aliases

- Verify: records why rv32 was not converted to aliases
- read the disposition record for the deferral


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-ARCH-COMMON-SBI-001 REQ-OS-ARCH-COMMON-SBI-002 REQ-OS-ARCH-COMMON-SBI-003 REQ-OS-ARCH-COMMON-SBI-004 REQ-OS-ARCH-COMMON-SBI-005 REQ-OS-ARCH-COMMON-SBI-006 REQ-OS-ARCH-COMMON-SBI-007
step("Verify: records why rv32 was not converted to aliases")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("read the disposition record for the deferral")
val doc = file_read("doc/08_tracking/todo/arch_common_wiring_wave2_2026-08-11.md")
expect(doc).to_contain("riscv32")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c94a41f1705ade89ccc85cedf2449205ab735b36615ce6fc2da472d14c755755`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c94a41f1705ade89ccc85cedf2449205ab735b36615ce6fc2da472d14c755755`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c94a41f1705ade89ccc85cedf2449205ab735b36615ce6fc2da472d14c755755`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/multiarch/arch_common_wave3_sbi_dedupe_spec.spl
mirror: doc/06_spec/01_unit/os/multiarch/arch_common_wave3_sbi_dedupe_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/multiarch/arch_common_wave3_sbi_dedupe_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/multiarch/arch_common_wave3_sbi_dedupe_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/multiarch/arch_common_wave3_sbi_dedupe_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
