# Cfg Dup Signature Dispatch Specification

> Tests covering seed native-build @cfg duplicate-signature arch dispatch.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cfg Dup Signature Dispatch Specification

## Scenarios

### seed native-build @cfg duplicate-signature arch dispatch

#### binds the active x86_64 @cfg variant when it is declared LAST (regression order)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- binds the active x86_64 @cfg variant when it is declared LAST (regression order)
   - Expected: compiled.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("binds the active x86_64 @cfg variant when it is declared LAST (regression order)")
val seed = _cfg_dup_seed_bin()
if file_exists(seed):
    val src_path = "/tmp/cfg_dup_signature_dispatch_repro_b.spl"
    val out_path = "/tmp/cfg_dup_signature_dispatch_repro_b.smf"
    file_write(src_path, _cfg_dup_source("riscv64", "arm64", "x86_64", "300", "200", "100"))
    file_delete(out_path)

    val compiled = shell("SIMPLE_RUST_SEED_WARNING=0 {seed} compile {src_path} -o {out_path} 2>&1")
    expect(compiled.exit_code).to_equal(0)

    val ran = shell("SIMPLE_RUST_SEED_WARNING=0 {seed} {out_path} 2>&1")

    # BUG: with riscv64 declared first, the seed's identical-signature
    # last-write-wins fallback binds the riscv64 body (got=300, FAIL)
    # on an x86_64 host instead of the active x86_64 body (got=100,
    # PASS) -- this assertion is expected to be RED until the fix
    # applies cfg-pruning ahead of this lowering path.
    expect(ran.stdout).to_contain("got=100")
    expect(ran.stdout).to_contain("PASS")

    file_delete(src_path)
    file_delete(out_path)
else:
    print("SKIP: seed binary not found at {seed} -- build via `cargo build --release --manifest-path src/compiler_rust/Cargo.toml` (see .claude/rules/bootstrap.md)")
```

</details>

#### binds the active x86_64 @cfg variant when it is declared FIRST (control order)

- binds the active x86_64 @cfg variant when it is declared FIRST (control order)
   - Expected: compiled.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("binds the active x86_64 @cfg variant when it is declared FIRST (control order)")
val seed = _cfg_dup_seed_bin()
if file_exists(seed):
    val src_path = "/tmp/cfg_dup_signature_dispatch_repro_a.spl"
    val out_path = "/tmp/cfg_dup_signature_dispatch_repro_a.smf"
    file_write(src_path, _cfg_dup_source("x86_64", "arm64", "riscv64", "100", "200", "300"))
    file_delete(out_path)

    val compiled = shell("SIMPLE_RUST_SEED_WARNING=0 {seed} compile {src_path} -o {out_path} 2>&1")
    expect(compiled.exit_code).to_equal(0)

    val ran = shell("SIMPLE_RUST_SEED_WARNING=0 {seed} {out_path} 2>&1")

    # Control: this order already passes today (first-declared happens
    # to coincide with the active arch), proving the harness itself is
    # sound and the failure above is order-dependent, not a broken test.
    expect(ran.stdout).to_contain("got=100")
    expect(ran.stdout).to_contain("PASS")

    file_delete(src_path)
    file_delete(out_path)
else:
    print("SKIP: seed binary not found at {seed} -- build via `cargo build --release --manifest-path src/compiler_rust/Cargo.toml` (see .claude/rules/bootstrap.md)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/cfg_dup_signature_dispatch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering seed native-build @cfg duplicate-signature arch dispatch.
- seed native-build @cfg duplicate-signature arch dispatch

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6a796093df81d8b34b051e8091b5aed3965da7dead2843d8dfb0f24dcc4bf703`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6a796093df81d8b34b051e8091b5aed3965da7dead2843d8dfb0f24dcc4bf703`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6a796093df81d8b34b051e8091b5aed3965da7dead2843d8dfb0f24dcc4bf703`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/driver/cfg_dup_signature_dispatch_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/cfg_dup_signature_dispatch_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/driver/cfg_dup_signature_dispatch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/cfg_dup_signature_dispatch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/cfg_dup_signature_dispatch_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/driver/cfg_dup_signature_dispatch_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds the active x86_64 @cfg variant when it is declared LAST (regression order)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/cfg_dup_signature_dispatch_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds the active x86_64 @cfg variant when it is declared FIRST (control order)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
