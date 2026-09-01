# incremental_missing_cache_file_spec

> Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# incremental_missing_cache_file_spec

Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/incremental_missing_cache_file_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience

Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

## Operator workflow

1. Run `bin/simple test test/01_unit/compiler/driver/incremental_missing_cache_file_spec.spl`.
2. Every scenario must pass; a failure is a regression in the behavior under test.

## Compatibility and limitations

Covers the behavior asserted here; platform-specific behavior is out of scope.

## Scenarios

### incremental cache reads on a missing file

#### hashes content through the std sha256_text facade (runtime oracle)

- Verify: hashes content through the std sha256_text facade (runtime oracle)


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: hashes content through the std sha256_text facade (runtime oracle)")
# The lexical claim (raw file ops stay under minimal unsafe authority and
# digests route through std sha256_text) is observed at runtime: the
# hash facade must produce the canonical SHA-256 of its input.
expect(incremental_hash_text("abc")).to_equal(
    "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")
expect(incremental_hash_text("")).to_equal(
    "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
```

</details>

#### read returns nil (not empty text) for a missing path

- Verify: read returns nil (not empty text) for a missing path


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: read returns nil (not empty text) for a missing path")
val got = incremental_file_read_text(missing)
expect got == nil
```

</details>

#### parse of a missing cache file is an Err, never a parse of nil

- Verify: parse of a missing cache file is an Err, never a parse of nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: parse of a missing cache file is an Err, never a parse of nil")
val r = incremental_parse_file(missing)
expect r.is_err()
```

</details>

#### fingerprint of a missing file is a miss

- Verify: fingerprint of a missing file is a miss


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: fingerprint of a missing file is a miss")
# @req: REQ-SSPEC-LOCAL-001
expect FileFingerprint.from_file(missing) == nil
```

</details>

#### dependency interface fold over a missing dep fails closed (nil)

- Verify: dependency interface fold over a missing dep fails closed (nil)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: dependency interface fold over a missing dep fails closed (nil)")
# @req: REQ-SSPEC-LOCAL-001
expect incremental_dependency_interface_fold([missing]) == nil
```

</details>

#### BuildCache.load on a missing cache path yields an empty cache

- Verify: BuildCache.load on a missing cache path yields an empty cache


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: BuildCache.load on a missing cache path yields an empty cache")
val cache = BuildCache.load(missing)
expect cache.entries.keys().len() == 0
```

</details>

#### fingerprint of an existing binary (non-UTF-8) file is NOT a miss

- Verify: fingerprint of an existing binary (non-UTF-8) file is NOT a miss


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: fingerprint of an existing binary (non-UTF-8) file is NOT a miss")
# rt_file_read_text is nil for non-UTF-8 bytes; native capsule receipts
# fingerprint .o files through this path, so nil-text must fall back to
# a byte digest rather than report the object as missing.
val fp = FileFingerprint.from_file("/bin/sh")
expect fp != nil
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9da8e975640e2b1af16560d89e6a4136b6fdb8410f9c5f1c63dc48acfc197afd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9da8e975640e2b1af16560d89e6a4136b6fdb8410f9c5f1c63dc48acfc197afd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9da8e975640e2b1af16560d89e6a4136b6fdb8410f9c5f1c63dc48acfc197afd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/driver/incremental_missing_cache_file_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/incremental_missing_cache_file_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/driver/incremental_missing_cache_file_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/incremental_missing_cache_file_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/incremental_missing_cache_file_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'hashes content through the std sha256_text facade (runtime oracle)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/incremental_missing_cache_file_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'read returns nil (not empty text) for a missing path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/incremental_missing_cache_file_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parse of a missing cache file is an Err, never a parse of nil' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

<!-- doc06-layout-migration: Historical generated/manual evidence retained; authoritative executable source remains at test/01_unit/compiler/driver/incremental_missing_cache_file_spec.spl. -->
