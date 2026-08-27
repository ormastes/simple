# Registry Publish

> Tests the package registry publish workflow including package validation, version bumping, and upload to the Simple package registry. Verifies that metadata, checksums, and dependency declarations are correctly assembled.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Registry Publish

Tests the package registry publish workflow including package validation, version bumping, and upload to the Simple package registry. Verifies that metadata, checksums, and dependency declarations are correctly assembled.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | In Progress |
| Source | `test/03_system/feature/app/publish_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the package registry publish workflow including package validation,
version bumping, and upload to the Simple package registry. Verifies that
metadata, checksums, and dependency declarations are correctly assembled.

## Scenarios

### Publish Command

#### when manifest is valid

#### parses package name from manifest

- parses package name from manifest
   - Expected: info[0] equals `my-pkg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses package name from manifest")
val content = "package:\n  name: my-pkg\n  version: 1.0.0\n"
val info = parse_manifest(content)
expect(info[0]).to_equal("my-pkg")
```

</details>

#### parses package version from manifest

- parses package version from manifest
   - Expected: info[1] equals `2.1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses package version from manifest")
val content = "package:\n  name: my-pkg\n  version: 2.1.0\n"
val info = parse_manifest(content)
expect(info[1]).to_equal("2.1.0")
```

</details>

#### when manifest is missing

#### returns error when no simple.sdn exists

- returns error when no simple.sdn exists
   - Expected: code equals `1`
   - Expected: (out + err) does not contain `Publishing `


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns error when no simple.sdn exists")
setup_publish_empty_dir()
val (out, err, code) = run_publish(["--dry-run"])
expect(code).to_equal(1)
expect((out + err).contains("Publishing ")).to_equal(false)
```

</details>

#### when using --dry-run

#### does not push to GHCR in dry-run mode

- does not push to GHCR in dry-run mode
   - Expected: code equals `0`
   - Expected: out does not contain `Pushing to GHCR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not push to GHCR in dry-run mode")
setup_publish_fixture("package:\n  name: dry-pkg\n  version: 3.4.5")
val (out, err, code) = run_publish(["--dry-run"])
expect(code).to_equal(0)
expect(out).to_contain("Publishing dry-pkg@3.4.5")
expect(out).to_contain("(dry run - no changes made)")
expect(out.contains("Pushing to GHCR")).to_equal(false)
```

</details>

### SPK Tarball

#### when building tarball

#### excludes .jj directory

- excludes .jj directory
   - Expected: should_include_in_spk(".jj/store/op_heads") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("excludes .jj directory")
expect(should_include_in_spk(".jj/store/op_heads")).to_equal(false)
```

</details>

#### excludes target directory

- excludes target directory
   - Expected: should_include_in_spk("target/pkg/app.spk") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("excludes target directory")
expect(should_include_in_spk("target/pkg/app.spk")).to_equal(false)
```

</details>

#### excludes .env files

- excludes .env files
   - Expected: should_include_in_spk("local.env") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("excludes .env files")
expect(should_include_in_spk("local.env")).to_equal(false)
```

</details>

#### includes simple.sdn manifest

- includes simple.sdn manifest
   - Expected: should_include_in_spk("simple.sdn") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("includes simple.sdn manifest")
expect(should_include_in_spk("simple.sdn")).to_equal(true)
```

</details>

#### includes src directory

- includes src directory
   - Expected: should_include_in_spk("src/main.spl") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("includes src directory")
expect(should_include_in_spk("src/main.spl")).to_equal(true)
```

</details>

### Checksum

#### computes sha256 checksum with prefix

- computes sha256 checksum with prefix
   - Expected: valid_sha256_checksum("sha256:0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef") is true
   - Expected: valid_sha256_checksum("0123456789abcdef") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("computes sha256 checksum with prefix")
# Checksum format: sha256:<hex>
expect(valid_sha256_checksum("sha256:0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef")).to_equal(true)
expect(valid_sha256_checksum("0123456789abcdef")).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `18b60a4833f3525936fa824dbe8f5920b953111bbcdb7a997bfad899c0829488`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `18b60a4833f3525936fa824dbe8f5920b953111bbcdb7a997bfad899c0829488`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `18b60a4833f3525936fa824dbe8f5920b953111bbcdb7a997bfad899c0829488`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/feature/app/publish_spec.spl
mirror: doc/06_spec/03_system/feature/app/publish_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/app/publish_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/app/publish_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/app/publish_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/app/publish_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses package name from manifest' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/publish_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses package version from manifest' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/publish_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns error when no simple.sdn exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
