# Target Architecture Specification

> Purpose: the target architecture facts (word width, pointer size, endianness) asserted in this spec. Audience: engineers reading this spec to confirm target model behavior still holds.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Target Architecture Specification

Purpose: the target architecture facts (word width, pointer size, endianness) asserted in this spec. Audience: engineers reading this spec to confirm target model behavior still holds.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #BM-ARCH-001 |
| Category | Bare-Metal / Architecture |
| Status | Implemented via std.common.target |
| Source | `test/03_system/feature/usage/target_arch_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience

Purpose: the target architecture facts (word width, pointer size, endianness) asserted in this spec. Audience: engineers reading this spec to confirm target model behavior still holds.

## Operator workflow

1. Run `bin/simple test test/03_system/feature/usage/target_arch_spec.spl`.
2. Every scenario must pass; a failure is a regression in the behavior under test.

## Compatibility and limitations

Covers std.common.target facts for named architectures and the host; board-specific behavior is out of scope.

## Scenarios

### Target Architecture Bit Widths

#### Named 8/16-bit architectures

#### resolves AVR and MCS51 to 8-bit words

- Parse the 8-bit aliases and read bits()


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Parse the 8-bit aliases and read bits()")
match parse_target_arch("avr"):
    case Some(arch): assert_equal(arch.bits(), 8)
    case None: fail("avr did not parse")
match parse_target_arch("mcs51"):
    case Some(arch): assert_equal(arch.bits(), 8)
    case None: fail("mcs51 did not parse")
```

</details>

#### resolves MSP430 and i8086 to 16-bit words

- Parse the 16-bit aliases and read bits()


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Parse the 16-bit aliases and read bits()")
match parse_target_arch("msp430"):
    case Some(arch): assert_equal(arch.bits(), 16)
    case None: fail("msp430 did not parse")
match parse_target_arch("8086"):
    case Some(arch): assert_equal(arch.bits(), 16)
    case None: fail("8086 did not parse")
```

</details>

#### Named 32/64-bit architectures

#### resolves x86 and wasm32 to 32-bit words

- Parse the 32-bit aliases and read bits()


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Parse the 32-bit aliases and read bits()")
match parse_target_arch("i386"):
    case Some(arch): assert_equal(arch.bits(), 32)
    case None: fail("i386 did not parse")
match parse_target_arch("wasm32"):
    case Some(arch): assert_equal(arch.bits(), 32)
    case None: fail("wasm32 did not parse")
```

</details>

#### resolves x86_64 and riscv64 to 64-bit words with 8-byte pointers

- Parse the 64-bit aliases and read bits()/pointer_size()


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Parse the 64-bit aliases and read bits()/pointer_size()")
match parse_target_arch("amd64"):
    case Some(arch):
        assert_equal(arch.bits(), 64)
        assert_equal(arch.pointer_size().bytes(), 8)
    case None: fail("amd64 did not parse")
match parse_target_arch("rv64"):
    case Some(arch): assert_equal(arch.bits(), 64)
    case None: fail("rv64 did not parse")
```

</details>

#### Host architecture

#### reports a 64-bit little-endian host on this machine

- Read TargetArch.host() and Endian.host()


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Read TargetArch.host() and Endian.host()")
val host = TargetArch.host()
assert_equal(host.bits(), 64)
assert_equal(Endian.host() == Endian.Little, true)
```

</details>

#### rejects an unknown architecture name

- Parse a nonexistent alias


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Parse a nonexistent alias")
assert_true(parse_target_arch("not-an-arch").to_be_nil())
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5238ca9b3b3955d6dd1ac121c96891f658d0a79ac29abda9b26e3832390bdaa0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5238ca9b3b3955d6dd1ac121c96891f658d0a79ac29abda9b26e3832390bdaa0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5238ca9b3b3955d6dd1ac121c96891f658d0a79ac29abda9b26e3832390bdaa0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/target_arch_spec.spl
mirror: doc/06_spec/03_system/feature/usage/target_arch_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/target_arch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/target_arch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/target_arch_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves AVR and MCS51 to 8-bit words' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/target_arch_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves MSP430 and i8086 to 16-bit words' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/target_arch_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves x86 and wasm32 to 32-bit words' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
