# In-process dynlib counterpart transport — load, call, compare

> Three lanes independently concluded that a counterpart spec could not execute

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# In-process dynlib counterpart transport — load, call, compare

Three lanes independently concluded that a counterpart spec could not execute

## At a Glance

| Field | Value |
|-------|-------|
| Category | Infrastructure |
| Status | Active |
| Design | doc/05_design/infra/counterpart/counterpart_conformance_infrastructure_design_2026-08-09.md |
| Source | `test/01_unit/infra/counterpart/dynlib_load_compare_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Three lanes independently concluded that a counterpart spec could not execute
an in-process shared library and substituted a hand-authored literal for its
output. That conclusion was wrong for the SUBPROCESS transport — this
scenario is for the OTHER transport nobody had exercised: loading a plain
system shared library (not a purpose-built `scf_get_api` adapter) and calling
a real exported C function directly, in-process.

The subject under test is `dynlib_digest_compare`
(`src/lib/nogc_sync_mut/spec/evidence/counterpart/dynlib_provider.spl`), which
dlopens a library, dlsyms a symbol, calls it against real memory, and compares
the result against a published NIST known-answer value. A red result here is a
real defect in the load/call/compare path, never a stand-in for one.

## Scope and Preconditions

Requires `/usr/lib/x86_64-linux-gnu/libcrypto.so.3` (OpenSSL) to be installed
and loadable on the host. When it is not present, the missing-library scenario
below is exactly the case this spec also proves: `unavailable`, not a silent
skip.

## Primary Workflow

Load `libcrypto.so.3`, call `SHA256(ptr, len, out[32])` against a known input,
hex-encode the 32-byte digest, and compare it to the published NIST vector.

## Key Concepts

| Concept | Description |
|---------|-------------|
| KAT | Known-Answer Test — an externally published expected value, never self-produced |
| `ProviderStatus.unavailable` | Fail-closed result for a missing library or symbol |
| `artifact_hash` | Real measured digest of the loaded library's own file bytes |

## Related Specifications

- [Frozen counterpart contracts](../../../../src/lib/common/spec/evidence/counterpart/model.spl)
- [Generic dlopen/dlsym SFFI](../../../../src/lib/nogc_sync_mut/sffi/dynamic.spl)

## Evidence and Provenance

Every digest in this scenario is computed by a real dlopen'd `libcrypto.so.3`
at run time. The expected values are the published NIST SHA-256 test vectors
for the empty string and for `"abc"` — never values this spec produced itself.

## Recovery and Troubleshooting

`unavailable` with detail `library not loadable` means libcrypto.so.3 is
missing from this host — install `libssl3` / `openssl`. `unavailable` with
detail `symbol not callable` means the installed libcrypto does not export
`SHA256` under that name (unlikely on any OpenSSL 1.x/3.x build).

## Scenarios

### In-process dynlib counterpart transport

#### computes the published SHA-256 of the empty string via a real dlopen'd libcrypto

- computes the published SHA-256 of the empty string via a real dlopen'd libcrypto
- Load libcrypto.so.3, call SHA256 on the empty string, compare to the NIST vector
- Confirm the run executed and the digest matches the published vector
- Confirm artifact_hash is a real measured digest, never an empty placeholder


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("computes the published SHA-256 of the empty string via a real dlopen'd libcrypto")
step("Load libcrypto.so.3, call SHA256 on the empty string, compare to the NIST vector")
val outcome = dynlib_digest_compare(LIBCRYPTO, "SHA256", "", 32, SHA256_EMPTY)
step("Confirm the run executed and the digest matches the published vector")
assert_equal(outcome.status, ProviderStatus.executed)
assert_true(outcome.matched)
assert_equal(outcome.digest_hex, SHA256_EMPTY)
step("Confirm artifact_hash is a real measured digest, never an empty placeholder")
assert_true(outcome.provenance.package_manifest_hash.len() == 64)
assert_true(outcome.artifact.canonical_hash != "")
```

</details>

#### computes the published SHA-256 of \

- computes the published SHA-256 of \
- Load libcrypto.so.3, call SHA256 on "abc", compare to the NIST vector
- Confirm the run executed and the digest matches the published vector


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("computes the published SHA-256 of \")
step("Load libcrypto.so.3, call SHA256 on \"abc\", compare to the NIST vector")
val outcome = dynlib_digest_compare(LIBCRYPTO, "SHA256", "abc", 32, SHA256_ABC)
step("Confirm the run executed and the digest matches the published vector")
assert_equal(outcome.status, ProviderStatus.executed)
assert_true(outcome.matched)
assert_equal(outcome.digest_hex, SHA256_ABC)
```

</details>

#### reports unavailable and rejects the run when the library does not exist

- reports unavailable and rejects the run when the library does not exist
- Load a library path that is not present on this host
- Confirm the run is rejected as unavailable, never faked with a literal digest


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("reports unavailable and rejects the run when the library does not exist")
step("Load a library path that is not present on this host")
val outcome = dynlib_digest_compare(MISSING_LIB, "SHA256", "abc", 32, SHA256_ABC)
step("Confirm the run is rejected as unavailable, never faked with a literal digest")
assert_equal(outcome.status, ProviderStatus.unavailable)
assert_false(outcome.matched)
assert_equal(outcome.digest_hex, "")
assert_true(outcome.detail.starts_with("library not loadable"))
```

</details>

#### reports unavailable and rejects the run when the symbol does not exist

- reports unavailable and rejects the run when the symbol does not exist
- Load the real libcrypto.so.3 but ask for a symbol it does not export
- Confirm the run is rejected as unavailable, never faked with a literal digest


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("reports unavailable and rejects the run when the symbol does not exist")
step("Load the real libcrypto.so.3 but ask for a symbol it does not export")
val outcome = dynlib_digest_compare(LIBCRYPTO, "SCF_NO_SUCH_SYMBOL_EVER", "abc", 32, SHA256_ABC)
step("Confirm the run is rejected as unavailable, never faked with a literal digest")
assert_equal(outcome.status, ProviderStatus.unavailable)
assert_false(outcome.matched)
assert_equal(outcome.digest_hex, "")
```

</details>

#### goes RED when the expected vector is sabotaged, naming the mismatch

- goes RED when the expected vector is sabotaged, naming the mismatch
- Corrupt one byte of the expected digest — the classic sabotage-must-fail check
- Confirm the comparator itself reports the mismatch rather than passing vacuously
- Restore: the corrupted vector above is a local literal, never written back to SHA256_EMPTY


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("goes RED when the expected vector is sabotaged, naming the mismatch")
step("Corrupt one byte of the expected digest — the classic sabotage-must-fail check")
val corrupted_vector = "ffffffff98fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
val outcome = dynlib_digest_compare(LIBCRYPTO, "SHA256", "", 32, corrupted_vector)
step("Confirm the comparator itself reports the mismatch rather than passing vacuously")
assert_equal(outcome.status, ProviderStatus.executed)
assert_false(outcome.matched)
assert_true(outcome.detail.starts_with("digest MISMATCH"))
step("Restore: the corrupted vector above is a local literal, never written back to SHA256_EMPTY")
assert_equal(SHA256_EMPTY, "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Design:** `doc/05_design/infra/counterpart/counterpart_conformance_infrastructure_design_2026-08-09.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-COUNTERPART-DYNLIB-001`
- `REQ-SSPEC-INFRA`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `22f3c423ee5504a045a871f670414321cd95c2e0396c5f8491abf2af75a8592d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `22f3c423ee5504a045a871f670414321cd95c2e0396c5f8491abf2af75a8592d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `22f3c423ee5504a045a871f670414321cd95c2e0396c5f8491abf2af75a8592d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/infra/counterpart/dynlib_load_compare_spec.spl
mirror: doc/06_spec/01_unit/infra/counterpart/dynlib_load_compare_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/infra/counterpart/dynlib_load_compare_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/infra/counterpart/dynlib_load_compare_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/infra/counterpart/dynlib_load_compare_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/infra/counterpart/dynlib_load_compare_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes the published SHA-256 of the empty string via a real dlopen'd libcrypto' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/infra/counterpart/dynlib_load_compare_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes the published SHA-256 of \' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/infra/counterpart/dynlib_load_compare_spec.spl:114:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports unavailable and rejects the run when the library does not exist' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
