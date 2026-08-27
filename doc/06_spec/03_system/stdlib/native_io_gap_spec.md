# Native Io Gap Specification

> Tests covering Native I/O Integration, file operations end-to-end, CLI arg parsing end-to-end, mapped types end-to-end, mmap struct API, cross-module integration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Io Gap Specification

## Scenarios

### Native I/O Integration

### file operations end-to-end

#### complete file lifecycle

- complete file lifecycle
   - Expected: wrote is true
   - Expected: file_exists(path) is true
   - Expected: deleted is true
   - Expected: file_exists(path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("complete file lifecycle")
dir_create_all(TEST_DIR)
val path = TEST_DIR + "/lifecycle.txt"
val wrote = file_write(path, "native io test content")
expect(wrote).to_equal(true)
expect(file_exists(path)).to_equal(true)
val content = file_read(path)
expect(content).to_contain("native io test content")
val sz = file_size(path)
expect(sz).to_be_greater_than(0)
val deleted = file_delete(path)
expect(deleted).to_equal(true)
expect(file_exists(path)).to_equal(false)
dir_remove_all(TEST_DIR)
```

</details>

### CLI arg parsing end-to-end

#### full CLI workflow

- full CLI workflow
   - Expected: parsed_flag(parsed, "verbose") is true
   - Expected: parsed_option(parsed, "output") equals `result.txt`
   - Expected: parsed_positional(parsed, 0) equals `input.spl`
   - Expected: result.0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("full CLI workflow")
val spec = cli_spec()
val spec2 = cli_spec_program(spec, "test-tool", "A system test tool")
val spec3 = cli_spec_flag(spec2, "verbose", "v", "Verbose output")
val spec4 = cli_spec_option(spec3, "output", "o", "Output file", "out.txt", [])
val spec5 = cli_spec_positional(spec4, "input", "Input file", true)
val parsed = parse_cli_args(spec5, ["-v", "--output", "result.txt", "input.spl"])
expect(parsed_flag(parsed, "verbose")).to_equal(true)
expect(parsed_option(parsed, "output")).to_equal("result.txt")
expect(parsed_positional(parsed, 0)).to_equal("input.spl")
val result = validate_args(spec5, parsed)
expect(result.0).to_equal(true)
val help = generate_help(spec5)
expect(help).to_contain("test-tool")
expect(help).to_contain("Verbose output")
```

</details>

### mapped types end-to-end

#### all type transforms produce correct output

- all type transforms produce correct output
   - Expected: partial("Config") equals `Partial<Config>`
   - Expected: readonly_type("Config") equals `Readonly<Config>`
   - Expected: pick_type("User", "name,email") equals `Pick<User, name,email>`
   - Expected: omit_type("User", "password") equals `Omit<User, password>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("all type transforms produce correct output")
expect(partial("Config")).to_equal("Partial<Config>")
expect(readonly_type("Config")).to_equal("Readonly<Config>")
expect(pick_type("User", "name,email")).to_equal("Pick<User, name,email>")
expect(omit_type("User", "password")).to_equal("Omit<User, password>")
```

</details>

### mmap struct API

#### rejects invalid mmap operations

- rejects invalid mmap operations
   - Expected: mf.address equals `0`
   - Expected: mf.size equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects invalid mmap operations")
val mf = MappedFile(address: 0, size: 0, path: "/nonexistent")
expect(mf.address).to_equal(0)
expect(mf.size).to_equal(0)
```

</details>

### cross-module integration

#### writes CLI-parsed output path

- writes CLI-parsed output path
   - Expected: file_exists(out_path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("writes CLI-parsed output path")
dir_create_all(TEST_DIR)
val spec = cli_spec()
val spec2 = cli_spec_option(spec, "output", "o", "Output file", "", [])
val parsed = parse_cli_args(spec2, ["--output", TEST_DIR + "/cli_out.txt"])
val out_path = parsed_option(parsed, "output")
file_write(out_path, "written via CLI path")
expect(file_exists(out_path)).to_equal(true)
val content = file_read(out_path)
expect(content).to_contain("written via CLI path")
dir_remove_all(TEST_DIR)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/stdlib/native_io_gap_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Native I/O Integration, file operations end-to-end, CLI arg parsing end-to-end, mapped types end-to-end, mmap struct API, cross-module integration.
- Native I/O Integration
- file operations end-to-end
- CLI arg parsing end-to-end
- mapped types end-to-end
- mmap struct API
- cross-module integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-native-io-gap`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d252e6b4fd980ca715be2346c2570786192453f95be0c09a2e38bef9394af4a7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d252e6b4fd980ca715be2346c2570786192453f95be0c09a2e38bef9394af4a7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d252e6b4fd980ca715be2346c2570786192453f95be0c09a2e38bef9394af4a7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/stdlib/native_io_gap_spec.spl
mirror: doc/06_spec/03_system/stdlib/native_io_gap_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=80
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/03_system/stdlib/native_io_gap_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/stdlib/native_io_gap_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/stdlib/native_io_gap_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/stdlib/native_io_gap_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/stdlib/native_io_gap_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'complete file lifecycle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/stdlib/native_io_gap_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'full CLI workflow' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/stdlib/native_io_gap_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'all type transforms produce correct output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
