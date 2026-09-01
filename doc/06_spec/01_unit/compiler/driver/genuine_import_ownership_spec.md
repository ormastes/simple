# Contract spec: test/01_unit/compiler/driver/genuine_import_ownership_spec.spl

> Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Contract spec: test/01_unit/compiler/driver/genuine_import_ownership_spec.spl

Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/genuine_import_ownership_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable
contracts red-visible, so a regression in the owned code fails this spec
instead of shipping silently.

## Scope and Preconditions

Precondition: the repository working tree holds the subject code under test.
Each scenario exercises the subject and asserts its observable contract; no
behavior outside the named subject is claimed.

## Primary Workflow

Run the scenarios; each one drives the subject through its pinned contract
and asserts the expected observable outcome with an executed oracle.

## Unsupported / Limitations

Only the pinned contracts are asserted here; end-to-end and integration
behavior of the surrounding system is covered by companion specs.

## Verification and Recovery

A red scenario names the contract that regressed. Recover by restoring the
pinned behavior in the subject; verify with
`bin/simple test test/01_unit/compiler/driver/genuine_import_ownership_spec.spl` and a green Results line.

## Scenarios

### genuine import ownership

#### binds handler compile and check symbols to their leaf owners

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- binds handler compile and check symbols to their leaf owners


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("binds handler compile and check symbols to their leaf owners")
val source = file_read("src/app/io/_CliCommands/handler_commands.spl")
expect(source).to_contain(r"use compiler.driver.driver_api_core.{interpret_file, check_file}")
expect(source).to_contain(r"use compiler.driver.driver_types.{CompileResult}")
expect(source).to_contain(r"use app.io.cli_compile.{cli_compile}")
```

</details>

#### does not rely on the circular command facade for compile-driver symbols

- does not rely on the circular command facade for compile-driver symbols


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not rely on the circular command facade for compile-driver symbols")
val source = file_read("src/app/io/_CliCommands/handler_commands.spl")
val owner_prefix = source.substring(0, source.find("fn cli_run_i18n"))
expect(owner_prefix).to_contain("use app.io.cli_commands.*")
expect(owner_prefix).to_contain(r"use app.io.cli_compile.{cli_compile}")
expect(owner_prefix).to_contain(r"use compiler.driver.driver_api_core.{interpret_file, check_file}")
```

</details>

#### imports SdnValue at module scope in both db_atomic implementations

- imports SdnValue at module scope in both db_atomic implementations


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("imports SdnValue at module scope in both db_atomic implementations")
for path in [
    "src/lib/nogc_sync_mut/db_atomic.spl",
    "src/lib/nogc_async_mut/db_atomic.spl"
]:
    val source = file_read(path)
    expect(source).to_contain(r"use std.sdn.{SdnValue}" + "\n")
    expect(source).to_not_contain(r"    use std.sdn.{SdnValue}")            expect(source).to_not_contain(r"use std.sdn.{parse, SdnValue}")            expect(source).to_contain(r"use std.sdn.{parse}")
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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a197064acee03a545fe4e622d49013a12b68b76ed0f1a155b70fd1d1c1d9680b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a197064acee03a545fe4e622d49013a12b68b76ed0f1a155b70fd1d1c1d9680b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a197064acee03a545fe4e622d49013a12b68b76ed0f1a155b70fd1d1c1d9680b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **95/100**; effective score: **95/100**; blockers: **0**.

SSpec documentization score: 95/100
source: test/01_unit/compiler/driver/genuine_import_ownership_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/genuine_import_ownership_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=100
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
test/01_unit/compiler/driver/genuine_import_ownership_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds handler compile and check symbols to their leaf owners' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/genuine_import_ownership_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not rely on the circular command facade for compile-driver symbols' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/genuine_import_ownership_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'imports SdnValue at module scope in both db_atomic implementations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
