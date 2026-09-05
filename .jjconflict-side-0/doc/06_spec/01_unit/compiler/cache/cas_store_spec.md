# Cas Store Specification

> Tests covering CAS blob store, CAS action manifests, CAS schema versioning.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cas Store Specification

## Scenarios

### CAS blob store

#### round-trips content and digest matches sha256 of content

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- round-trips content and digest matches sha256 of content
   - Expected: digest equals `sha256_text(content)`
   - Expected: cas_get(root, digest) ?? "<absent>" equals `content`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("round-trips content and digest matches sha256 of content")
val root = fresh_root()
val content = "hello cas blob"
val digest = cas_put(root, content)
expect(digest).to_equal(sha256_text(content))
expect(cas_get(root, digest) ?? "<absent>").to_equal(content)
```

</details>

#### dedups identical content on repeated put

- dedups identical content on repeated put
   - Expected: d1 equals `d2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("dedups identical content on repeated put")
val root = fresh_root()
val d1 = cas_put(root, "same bytes twice")
val d2 = cas_put(root, "same bytes twice")
expect(d1).to_equal(d2)
assert_true(d1 != "")
assert_true(cas_has(root, d1))
```

</details>

#### returns none for an absent digest

- returns none for an absent digest
   - Expected: cas_get(root, absent) ?? "<absent>" equals `<absent>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns none for an absent digest")
val root = fresh_root()
val absent = sha256_text("content that was never stored")
assert_false(cas_has(root, absent))
expect(cas_get(root, absent) ?? "<absent>").to_equal("<absent>")
```

</details>

#### detects corruption and never serves unverified bytes

- detects corruption and never serves unverified bytes
   - Expected: cas_get(root, digest) ?? "<absent>" equals `<absent>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("detects corruption and never serves unverified bytes")
val root = fresh_root()
val digest = cas_put(root, "pristine payload")
# Corrupt the blob on disk behind the store's back.
assert_true(rt_file_write_text(cas_blob_path(root, digest), "corrupt payload"))
expect(cas_get(root, digest) ?? "<absent>").to_equal("<absent>")
# Corrupt entry was quarantined, not left in place.
assert_false(cas_has(root, digest))
```

</details>

#### gives distinct digests to distinct contents, both retrievable

- gives distinct digests to distinct contents, both retrievable
   - Expected: cas_get(root, da) ?? "<absent>" equals `content alpha`
   - Expected: cas_get(root, db) ?? "<absent>" equals `content beta`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("gives distinct digests to distinct contents, both retrievable")
val root = fresh_root()
val da = cas_put(root, "content alpha")
val db = cas_put(root, "content beta")
assert_true(da != db)
expect(cas_get(root, da) ?? "<absent>").to_equal("content alpha")
expect(cas_get(root, db) ?? "<absent>").to_equal("content beta")
```

</details>

#### keeps slash/underscore collision pairs distinct (P1 flattening hole)

- keeps slash/underscore collision pairs distinct (P1 flattening hole)
   - Expected: cas_get(root, d1) ?? "<absent>" equals `a/b_c`
   - Expected: cas_get(root, d2) ?? "<absent>" equals `a_b/c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps slash/underscore collision pairs distinct (P1 flattening hole)")
# Under the legacy `/`->`_` path flattening, "a/b_c" and "a_b/c"
# collapse to the same cache path. Digest addressing must not.
val root = fresh_root()
val d1 = cas_put(root, "a/b_c")
val d2 = cas_put(root, "a_b/c")
assert_true(d1 != d2)
expect(cas_get(root, d1) ?? "<absent>").to_equal("a/b_c")
expect(cas_get(root, d2) ?? "<absent>").to_equal("a_b/c")
```

</details>

### CAS action manifests

#### round-trips an action manifest

- round-trips an action manifest
   - Expected: action_digest_of(got) equals `key`
   - Expected: artifact_count_of(got) equals `2`
   - Expected: artifact_at(got, 0) equals `a1`
   - Expected: artifact_at(got, 1) equals `a2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("round-trips an action manifest")
val root = fresh_root()
val key = sha256_text("action-key-1")
val a1 = sha256_text("artifact-one")
val a2 = sha256_text("artifact-two")
val manifest = ActionManifest(action_digest: key, artifact_digests: [a1, a2], schema_version: 1)
assert_true(action_put(root, key, manifest))
val got = action_get(root, key)
expect(action_digest_of(got)).to_equal(key)
expect(artifact_count_of(got)).to_equal(2)
expect(artifact_at(got, 0)).to_equal(a1)
expect(artifact_at(got, 1)).to_equal(a2)
```

</details>

#### rejects a mislabeled manifest at put time

- rejects a mislabeled manifest at put time


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects a mislabeled manifest at put time")
val root = fresh_root()
val key = sha256_text("action-key-2")
val wrong = ActionManifest(action_digest: sha256_text("other-key"), artifact_digests: [], schema_version: 1)
assert_false(action_put(root, key, wrong))
```

</details>

#### returns none for a tampered stored manifest

- returns none for a tampered stored manifest
   - Expected: action_digest_of(action_get(root, key)) equals `<absent>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns none for a tampered stored manifest")
val root = fresh_root()
val key = sha256_text("action-key-3")
val manifest = ActionManifest(action_digest: key, artifact_digests: [sha256_text("artifact")], schema_version: 1)
assert_true(action_put(root, key, manifest))
# Tamper: rewrite the stored manifest so it claims a different action key.
val forged = ActionManifest(action_digest: sha256_text("forged-key"), artifact_digests: [sha256_text("artifact")], schema_version: 1)
assert_true(rt_file_write_text(cas_action_path(root, key), action_manifest_serialize(forged)))
expect(action_digest_of(action_get(root, key))).to_equal("<absent>")
```

</details>

#### returns none for an absent action digest

- returns none for an absent action digest
   - Expected: action_digest_of(got) equals `<absent>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns none for an absent action digest")
val root = fresh_root()
val got = action_get(root, sha256_text("never stored action"))
expect(action_digest_of(got)).to_equal("<absent>")
```

</details>

### CAS schema versioning

#### treats a wrong-version store as empty and rewrites VERSION

- treats a wrong-version store as empty and rewrites VERSION
   - Expected: cas_get(root, digest) ?? "<absent>" equals `<absent>`
   - Expected: rt_file_read_text("{root}/VERSION").trim() equals `cas_version_text()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("treats a wrong-version store as empty and rewrites VERSION")
val root = fresh_root()
val digest = cas_put(root, "old schema payload")
assert_true(cas_has(root, digest))
# Simulate a schema bump: stamp a foreign version, reopen.
assert_true(rt_file_write_text("{root}/VERSION", "999"))
assert_true(cas_open(root))
# Old entries are never trusted after a schema mismatch.
assert_false(cas_has(root, digest))
expect(cas_get(root, digest) ?? "<absent>").to_equal("<absent>")
# VERSION was rewritten to the current schema.
expect(rt_file_read_text("{root}/VERSION").trim()).to_equal(cas_version_text())
```

</details>

#### resolves root from SIMPLE_CACHE with build/cache_cas default

- resolves root from SIMPLE_CACHE with build/cache_cas default
   - Expected: cas_root() equals `build/tmp/cas_store_spec/env-root`
   - Expected: cas_root() equals `build/cache_cas`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("resolves root from SIMPLE_CACHE with build/cache_cas default")
val saved = rt_env_get("SIMPLE_CACHE") ?? ""
rt_env_set("SIMPLE_CACHE", "build/tmp/cas_store_spec/env-root")
expect(cas_root()).to_equal("build/tmp/cas_store_spec/env-root")
rt_env_set("SIMPLE_CACHE", "")
expect(cas_root()).to_equal("build/cache_cas")
rt_env_set("SIMPLE_CACHE", saved)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/cache/cas_store_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CAS blob store, CAS action manifests, CAS schema versioning.
- CAS blob store
- CAS action manifests
- CAS schema versioning

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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

- Canonical SPipe generation for source `5e5f6949d9682643fbc575b931ae8a3009c80a4462148b3819bac30f3f0c400f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5e5f6949d9682643fbc575b931ae8a3009c80a4462148b3819bac30f3f0c400f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5e5f6949d9682643fbc575b931ae8a3009c80a4462148b3819bac30f3f0c400f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/cache/cas_store_spec.spl
mirror: doc/06_spec/01_unit/compiler/cache/cas_store_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/cache/cas_store_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/cache/cas_store_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/cache/cas_store_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/cache/cas_store_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips content and digest matches sha256 of content' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/cache/cas_store_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dedups identical content on repeated put' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/cache/cas_store_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns none for an absent digest' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
