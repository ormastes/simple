# Rv64 Boot Call Parser Specification

> Tests covering RV64 boot call parser.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rv64 Boot Call Parser Specification

## Scenarios

### RV64 boot call parser

#### parses the boot_main nested call sequence

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses the boot_main nested call sequence
   - Expected: decls.len() equals `8`
   - Expected: decl_get_tag(boot) equals `1`
   - Expected: decl_get_name(boot) equals `boot_main`
   - Expected: decl_get_body(boot).len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("parses the boot_main nested call sequence")
val decls = parse_rv64_boot_call_decls()

expect(decls.len()).to_equal(8)
val boot = decls[7]
expect(decl_get_tag(boot)).to_equal(1)
expect(decl_get_name(boot)).to_equal("boot_main")
expect(decl_get_body(boot).len()).to_equal(5)
```

</details>

#### bridges the boot_main nested call sequence

- bridges the boot_main nested call sequence
   - Expected: decls.len() equals `8`
   - Expected: decl_get_tag(decls[7]) equals `1`
   - Expected: decl_get_name(decls[7]) equals `boot_main`
   - Expected: boot.body.stmts.len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bridges the boot_main nested call sequence")
ast_reset()
parser_init_with_path(rv64_boot_call_source(), "")
parse_module_body()
val decls = module_get_decls()
expect(decls.len()).to_equal(8)
expect(decl_get_tag(decls[7])).to_equal(1)
expect(decl_get_name(decls[7])).to_equal("boot_main")

val module = flat_ast_to_module("src/os/kernel/arch/riscv64/boot.spl")
if not module.functions.contains("boot_main"):
    panic("missing boot_main function after flat bridge")
val boot = module.functions["boot_main"] ?? panic("missing boot_main function")

expect(boot.body.stmts.len()).to_equal(5)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/rv64_boot_call_parser_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RV64 boot call parser.
- RV64 boot call parser

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

- Canonical SPipe generation for source `fda3b55b6fdafdac65f55fafb704351a8d9fbb685f35ce117b50440fde119b37`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fda3b55b6fdafdac65f55fafb704351a8d9fbb685f35ce117b50440fde119b37`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fda3b55b6fdafdac65f55fafb704351a8d9fbb685f35ce117b50440fde119b37`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/parser/rv64_boot_call_parser_spec.spl
mirror: doc/06_spec/01_unit/compiler/parser/rv64_boot_call_parser_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/parser/rv64_boot_call_parser_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/parser/rv64_boot_call_parser_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/parser/rv64_boot_call_parser_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/parser/rv64_boot_call_parser_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses the boot_main nested call sequence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/rv64_boot_call_parser_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bridges the boot_main nested call sequence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
