# Replay Facade Specification

> Tests covering gc_async_mut replay facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Facade Specification

## Scenarios

### gc_async_mut replay facade

#### re-exports replay records, codec, and target types

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports replay records, codec, and target types
   - Expected: entry.event_kind() equals `EventKind.SyscallEnter`
   - Expected: encoded.len() as i64 equals `80`
   - Expected: decoded.thread_id equals `11`
   - Expected: decoded.event_kind() equals `EventKind.SyscallEnter`
   - Expected: Arch.RISCV64.pointer_bits() equals `64`
   - Expected: Address.for_arch(Arch.RISCV32, 0x1000).bits equals `32`
   - Expected: TargetDesc.for_arch(Arch.AARCH64).register_schema_id equals `aarch64-v1`
   - Expected: ReplayMode.Record.to_text() equals `record`
   - Expected: cfg.gdb_port equals `1234`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports replay records, codec, and target types")
val entry = ReplayEntry.create(EventKind.SyscallEnter, 11, 22, 1)
expect(entry.event_kind()).to_equal(EventKind.SyscallEnter)
val encoded = encode_entry(entry)
expect(encoded.len() as i64).to_equal(80)
val decoded = decode_entry(encoded, 0).unwrap()
expect(decoded.thread_id).to_equal(11)
expect(decoded.event_kind()).to_equal(EventKind.SyscallEnter)
expect(Arch.RISCV64.pointer_bits()).to_equal(64)
expect(Address.for_arch(Arch.RISCV32, 0x1000).bits).to_equal(32)
expect(TargetDesc.for_arch(Arch.AARCH64).register_schema_id).to_equal("aarch64-v1")
expect(ReplayMode.Record.to_text()).to_equal("record")
val cfg = ReplayConfig.for_replay(Arch.X86_64, "kernel.elf", "trace.srrq")
expect(cfg.gdb_port).to_equal(1234)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gc_async_mut/replay/replay_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gc_async_mut replay facade.
- gc_async_mut replay facade

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `cc7d94adf84df2d4f3c74748f05659f62a07709cda9696ecfc703222cf36663a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cc7d94adf84df2d4f3c74748f05659f62a07709cda9696ecfc703222cf36663a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cc7d94adf84df2d4f3c74748f05659f62a07709cda9696ecfc703222cf36663a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/unit/lib/gc_async_mut/replay/replay_facade_spec.spl
mirror: doc/06_spec/unit/lib/gc_async_mut/replay/replay_facade_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/gc_async_mut/replay/replay_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/gc_async_mut/replay/replay_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/gc_async_mut/replay/replay_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/gc_async_mut/replay/replay_facade_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports replay records, codec, and target types' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
