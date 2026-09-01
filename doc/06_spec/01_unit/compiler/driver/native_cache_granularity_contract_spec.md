# Native Cache Granularity Contract Specification

> Tests covering native object cache granularity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Cache Granularity Contract Specification

## Scenarios

### native object cache granularity

#### invalidates dependents when a provider changes from struct to class

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- invalidates dependents when a provider changes from struct to class
- Keep the dependent source unchanged across the ABI change
   - Expected: dependent.content equals `dependent.content`
- Require the source-closure fingerprint to invalidate dependent objects


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("invalidates dependents when a provider changes from struct to class")
val dependent = SourceFile(
    path: "consumer.spl",
    content: "use provider.\{Surface\}\nfn owner(value: Surface) -> text: value.owner",
    module_name: "consumer"
)
val struct_provider = SourceFile(
    path: "provider.spl",
    content: "pub struct Surface:\n    owner: text",
    module_name: "provider"
)
val class_provider = SourceFile(
    path: "provider.spl",
    content: "pub class Surface:\n    owner: text",
    module_name: "provider"
)

step("Keep the dependent source unchanged across the ABI change")
expect(dependent.content).to_equal(dependent.content)

step("Require the source-closure fingerprint to invalidate dependent objects")
val before = driver_native_sources_fingerprint([struct_provider, dependent])
val after = driver_native_sources_fingerprint([class_provider, dependent])
assert_not_equal(before, after)
```

</details>

#### keeps coarse invalidation until sound module dependency keys exist

- keeps coarse invalidation until sound module dependency keys exist
- Check producer and closure identities explain full refreshes
- Check dependency-free entries cannot safely use granular reuse


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps coarse invalidation until sound module dependency keys exist")
val incremental = file_read("src/compiler/80.driver/driver_build/incremental.spl")
val native_output = file_read("src/compiler/80.driver/driver_aot_native_output.spl")

step("Check producer and closure identities explain full refreshes")
expect(incremental).to_contain("native_build_compiler_source_fingerprint()")
# The bare "{hash}+src{src_fp}" fold was replaced by the full producer
# identity in ca5d0f50805; the compiler-source fingerprint is still folded in.
expect(incremental).to_contain("compiler=\{compiler_source_fingerprint\}")
expect(native_output).to_contain("driver_native_sources_fingerprint")
expect(native_output).to_contain("\"sources-\{sources_fingerprint\}\"")

step("Check dependency-free entries cannot safely use granular reuse")
# Renamed receiver in 809ce6d4e71 (BuildCache by-value persistence fix); the
# contract asserted here — an empty dependency list, i.e. coarse invalidation —
# is unchanged.
expect(native_output).to_contain("build_cache.update_entry(capsule.cache_source, source_fp_val, [], [object_path])")
expect(native_output).to_contain("val cached_outputs = build_cache.get_cached_outputs(cache_source)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/native_cache_granularity_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering native object cache granularity.
- native object cache granularity

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c3a703bff4a1d910d9eccd1958a91cc59bce3227433df7ad5fb6d118986b6cc3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c3a703bff4a1d910d9eccd1958a91cc59bce3227433df7ad5fb6d118986b6cc3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c3a703bff4a1d910d9eccd1958a91cc59bce3227433df7ad5fb6d118986b6cc3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/compiler/driver/native_cache_granularity_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/native_cache_granularity_contract_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/driver/native_cache_granularity_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/native_cache_granularity_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/native_cache_granularity_contract_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'invalidates dependents when a provider changes from struct to class' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/native_cache_granularity_contract_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps coarse invalidation until sound module dependency keys exist' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
