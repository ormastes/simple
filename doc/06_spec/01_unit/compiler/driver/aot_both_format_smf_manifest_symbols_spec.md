# Aot Both Format Smf Manifest Symbols Specification

> Tests covering AOT both-format SMF manifest update.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aot Both Format Smf Manifest Symbols Specification

## Scenarios

### AOT both-format SMF manifest update

#### records an SMF manifest entry for a freshly built source

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- records an SMF manifest entry for a freshly built source
- Stage a source file the AOT lane would have just compiled
- Derive the SMF cache path the same way the AOT branch does
- Record the manifest entry with the AOT call site's 10-argument shape
- Read the manifest back and confirm the entry is really there
   - Expected: entry.smf_path equals `smf_cache_path`
   - Expected: entry.source_hash equals `424242`
   - Expected: entry.backend equals `llvm`
   - Expected: entry.opt_level equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("records an SMF manifest entry for a freshly built source")
"""The AOT lane builds a native binary, compiles a sibling SMF into the
native build cache, and then records that SMF in the cache manifest so a
later run can reuse it instead of recompiling."""

step("Stage a source file the AOT lane would have just compiled")
val source_path = "/tmp/simple_aot_both_regression_src.spl"
file_write(source_path, "fn main():\n    print(\"hi\")\n")
expect(file_exists(source_path)).to_be(true)

step("Derive the SMF cache path the same way the AOT branch does")
val cache_dir = "/tmp/simple_aot_both_regression_cache"
val smf_cache_path = source_to_cache_path(source_path, cache_dir, ".smf")
expect(smf_cache_path).to_contain(".smf")

step("Record the manifest entry with the AOT call site's 10-argument shape")
val ok = update_smf_manifest_entry(
    source_path,
    smf_cache_path,
    424242,
    "llvm",
    2,
    true,
    false,
    false,
    "",
    []
)
expect(ok).to_be(true)

step("Read the manifest back and confirm the entry is really there")
val manifest = load_smf_manifest(smf_manifest_path_for_smf(smf_cache_path))
val found = smf_manifest_find(manifest, source_path)
expect(found != nil).to_be(true)
if val Some(entry) = found:
    expect(entry.smf_path).to_equal(smf_cache_path)
    expect(entry.source_hash).to_equal(424242)
    expect(entry.backend).to_equal("llvm")
    expect(entry.opt_level).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/aot_both_format_smf_manifest_symbols_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering AOT both-format SMF manifest update.
- AOT both-format SMF manifest update

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `85aa9982255808bbe3586ad173e17b9f867268a60ed4af19815591d766c8f7a9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `85aa9982255808bbe3586ad173e17b9f867268a60ed4af19815591d766c8f7a9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `85aa9982255808bbe3586ad173e17b9f867268a60ed4af19815591d766c8f7a9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/01_unit/compiler/driver/aot_both_format_smf_manifest_symbols_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/aot_both_format_smf_manifest_symbols_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/driver/aot_both_format_smf_manifest_symbols_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/aot_both_format_smf_manifest_symbols_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/aot_both_format_smf_manifest_symbols_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/driver/aot_both_format_smf_manifest_symbols_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records an SMF manifest entry for a freshly built source' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
