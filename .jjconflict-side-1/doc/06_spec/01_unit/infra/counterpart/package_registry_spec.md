# Counterpart Conformance — package and build resolver

> Before a conformance run compares anything, something has to decide whether the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Counterpart Conformance — package and build resolver

Before a conformance run compares anything, something has to decide whether the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Infrastructure |
| Status | In Progress |
| Plan | doc/03_plan/infra/counterpart/counterpart_conformance_parallel_agent_plan_2026-08-09.md |
| Design | doc/05_design/infra/counterpart/counterpart_conformance_infrastructure_design_2026-08-09.md |
| Source | `test/01_unit/infra/counterpart/package_registry_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Before a conformance run compares anything, something has to decide whether the
provider it is about to load is the one the lockfile pins. This scenario is for
the engineer landing a provider: it shows what the resolver accepts, and — the
part that matters — every distinct way it refuses.

The refusals are the product. A resolver that answers "close enough" turns a
supply-chain question into a coin flip, and a conformance suite that loads an
unverified binary is measuring something nobody pinned.

## Scope and Preconditions

The resolver reads two on-disk shapes: a provider descriptor under
`config/counterpart/providers/` and the lock records in
`config/counterpart/counterpart.lock.sdn`. Nothing here downloads, compiles or
dlopens anything; the digest of the artifact actually present on disk is passed
in as a value so that every negative path is reachable without staging a build
tree, and so the resolver has no way to substitute a hash it computed itself.

## Primary Workflow

An operator writes a descriptor and a lock record, builds the adapter into
`build/counterparts/<target>/<digest>/`, and asks the resolver to resolve it.
The answer is a status plus a verification state plus the reasons. A verified
provider is the only one a run may load.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Lock record | The pinned identity: revision, hashes, toolchain, target, SPDX |
| Build digest | Content address over every input that can change the artifact bytes |
| UNVERIFIED | A `pending` placeholder hash — never checked, and never "verified" |
| UNAVAILABLE | Missing, mismatched or absent. Never a pass |
| Fetch guard | The only network phase; refuses "latest", "HEAD" and unpinned records |

## Related Specifications

- `test/01_unit/infra/counterpart/contract_model_spec.spl` — the frozen contracts this consumes

## Evidence and Provenance

The happy-path descriptor below is byte-shaped after the landed
`config/counterpart/providers/mock.sdn`, and the lock fixture after the landed
`counterpart.lock.sdn`, so a schema change to either file surfaces here as a
parse failure rather than as a silent green.

## Recovery and Troubleshooting

Each refusal names the provider and the field. `UNVERIFIED` means the lockfile
still says `pending`: build the artifact, then record its digest in the lock.
`MISMATCH` means the bytes on disk are not the bytes that were pinned — that is
a supply-chain event, not a stale cache to be deleted quietly.

## Compatibility and Limitations

Resolution only. Passing here proves an unverified provider cannot be loaded;
it proves nothing about what the provider computes once it is.

## Scenarios

### Counterpart descriptor and lockfile reading

#### reads a provider descriptor including its component list

- reads a provider descriptor including its component list
- Parse a descriptor shaped after the landed mock provider
- Confirm the provider identity fields were read
   - Expected: descriptor.provider_id equals `mock`
   - Expected: descriptor.provider_kind equals `native_in_process`
   - Expected: descriptor.abi_version equals `1`
   - Expected: descriptor.license_spdx equals `Apache-2.0`
- Confirm the nested upstream and adapter sections were read
   - Expected: descriptor.upstream_kind equals `none`
   - Expected: descriptor.adapter_output equals `libsimple_counterpart_mock`
- Confirm the component and its declared relations were read
   - Expected: descriptor.components.len() equals `1`
   - Expected: descriptor.components[0].counterpart_boundary_id equals `mock.execution.echo@1`
   - Expected: descriptor.components[0].supported_relations.len() equals `2`
   - Expected: descriptor.parse_errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("reads a provider descriptor including its component list")
step("Parse a descriptor shaped after the landed mock provider")
val descriptor = a_wellformed_descriptor()
step("Confirm the provider identity fields were read")
expect(descriptor.provider_id).to_equal("mock")
expect(descriptor.provider_kind).to_equal("native_in_process")
expect(descriptor.abi_version).to_equal(1)
expect(descriptor.license_spdx).to_equal("Apache-2.0")
step("Confirm the nested upstream and adapter sections were read")
expect(descriptor.upstream_kind).to_equal("none")
expect(descriptor.adapter_output).to_equal("libsimple_counterpart_mock")
step("Confirm the component and its declared relations were read")
expect(descriptor.components.len()).to_equal(1)
expect(descriptor.components[0].counterpart_boundary_id).to_equal("mock.execution.echo@1")
expect(descriptor.components[0].supported_relations.len()).to_equal(2)
expect(descriptor.parse_errors.len()).to_equal(0)
```

</details>

#### reads a deliberately empty lock field without ending the record

- reads a deliberately empty lock field without ending the record
- Parse a lock entry whose upstream fields are the empty string
- Confirm the fields after the empty ones still belong to the record
   - Expected: records.len() equals `1`
   - Expected: records[0].provider_id equals `mock`
   - Expected: records[0].upstream_url equals ``
   - Expected: records[0].target_triple equals `x86_64-unknown-linux-gnu`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("reads a deliberately empty lock field without ending the record")
step("Parse a lock entry whose upstream fields are the empty string")
val records = parse_lock_file("counterpart_lock:\n"
    + "  schema_version: 1\n"
    + "  entries:\n"
    + "    - provider_id: mock\n"
    + "      upstream_url: \"\"\n"
    + "      source_archive_sha256: \"\"\n"
    + "      toolchain_identity: host-cc\n"
    + "      target_triple: x86_64-unknown-linux-gnu\n")
step("Confirm the fields after the empty ones still belong to the record")
expect(records.len()).to_equal(1)
expect(records[0].provider_id).to_equal("mock")
expect(records[0].upstream_url).to_equal("")
expect(records[0].target_triple).to_equal("x86_64-unknown-linux-gnu")
```

</details>

#### addresses the cache by target and build digest

- addresses the cache by target and build digest
- Compute the build digest for a descriptor and its lock record
- Confirm the digest is a stable content address, not empty
   - Expected: digest.len() equals `32`
- Confirm the cache path is rooted under build/counterparts/<target>/<digest>


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("addresses the cache by target and build digest")
step("Compute the build digest for a descriptor and its lock record")
val digest = build_digest(a_wellformed_descriptor(), a_lock_record_with(VERIFIED_HASH))
step("Confirm the digest is a stable content address, not empty")
expect(digest.len()).to_equal(32)
step("Confirm the cache path is rooted under build/counterparts/<target>/<digest>")
expect(cache_dir_for("x86_64-unknown-linux-gnu", digest)).to_equal(
    "build/counterparts/x86_64-unknown-linux-gnu/" + digest)
```

</details>

#### gives a different digest when the toolchain changes

- gives a different digest when the toolchain changes
- Compute the digest for the pinned toolchain
- Recompute it with a different toolchain identity
- Confirm the two builds do not share a cache directory


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("gives a different digest when the toolchain changes")
step("Compute the digest for the pinned toolchain")
val baseline = build_digest(a_wellformed_descriptor(), a_lock_record_with(VERIFIED_HASH))
step("Recompute it with a different toolchain identity")
var other = a_lock_record_with(VERIFIED_HASH)
other.toolchain_identity = "clang-19"
val moved = build_digest(a_wellformed_descriptor(), other)
step("Confirm the two builds do not share a cache directory")
expect(moved).to_not_equal(baseline)
```

</details>

### Counterpart verified resolution

#### resolves a pinned provider whose artifact hash matches the lock

- resolves a pinned provider whose artifact hash matches the lock
- Resolve a well-formed descriptor against a lock record with a real digest
- Confirm the provider is verified and usable
   - Expected: provider_status_name(resolved.status) equals `executed`
   - Expected: verification_state_name(resolved.verification) equals `verified`
- Confirm a verified resolution reports no reasons to refuse
   - Expected: resolved.reasons.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("resolves a pinned provider whose artifact hash matches the lock")
step("Resolve a well-formed descriptor against a lock record with a real digest")
val resolved = resolve_provider(
    a_wellformed_descriptor(),
    [a_lock_record_with(VERIFIED_HASH)],
    VERIFIED_HASH
)
step("Confirm the provider is verified and usable")
expect(provider_status_name(resolved.status)).to_equal("executed")
expect(verification_state_name(resolved.verification)).to_equal("verified")
assert_true(verification_state_is_verified(resolved.verification))
assert_true(resolved_provider_is_usable(resolved))
step("Confirm a verified resolution reports no reasons to refuse")
expect(resolved.reasons.len()).to_equal(0)
```

</details>

### Counterpart resolver refusals

#### reports a provider with no lock record as unavailable rather than passing it

- reports a provider with no lock record as unavailable rather than passing it
- Resolve a descriptor against a lockfile that does not mention it
- Confirm the provider is UNAVAILABLE, not executed
   - Expected: provider_status_name(resolved.status) equals `unavailable`
   - Expected: verification_state_name(resolved.verification) equals `lock_missing`
- Confirm it is not usable and says why


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("reports a provider with no lock record as unavailable rather than passing it")
step("Resolve a descriptor against a lockfile that does not mention it")
val resolved = resolve_provider(a_wellformed_descriptor(), [], VERIFIED_HASH)
step("Confirm the provider is UNAVAILABLE, not executed")
expect(provider_status_name(resolved.status)).to_equal("unavailable")
expect(verification_state_name(resolved.verification)).to_equal("lock_missing")
step("Confirm it is not usable and says why")
assert_false(resolved_provider_is_usable(resolved))
expect(resolved.reasons.len()).to_be_greater_than(0)
```

</details>

#### refuses an artifact whose hash disagrees with the lock

- refuses an artifact whose hash disagrees with the lock
- Resolve with an on-disk digest that is not the pinned one
- Confirm the mismatch is named as a mismatch, not as a missing provider
   - Expected: verification_state_name(resolved.verification) equals `hash_mismatch`
   - Expected: provider_status_name(resolved.status) equals `unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("refuses an artifact whose hash disagrees with the lock")
step("Resolve with an on-disk digest that is not the pinned one")
val resolved = resolve_provider(
    a_wellformed_descriptor(),
    [a_lock_record_with(VERIFIED_HASH)],
    "0000000000000000000000000000000000000000000000000000000000000000"
)
step("Confirm the mismatch is named as a mismatch, not as a missing provider")
expect(verification_state_name(resolved.verification)).to_equal("hash_mismatch")
expect(provider_status_name(resolved.status)).to_equal("unavailable")
assert_false(resolved_provider_is_usable(resolved))
```

</details>

#### reports a pending placeholder hash as unverified and never as verified

- reports a pending placeholder hash as unverified and never as verified
- Resolve against a lock record whose artifact hash is still the placeholder
- Confirm the state is UNVERIFIED, distinct from both verified and mismatched
   - Expected: verification_state_name(resolved.verification) equals `unverified_placeholder`
- Confirm a placeholder cannot masquerade as a checked hash even when the observed digest equals it
   - Expected: verification_state_name(echoed.verification) equals `unverified_placeholder`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("reports a pending placeholder hash as unverified and never as verified")
step("Resolve against a lock record whose artifact hash is still the placeholder")
assert_true(hash_is_placeholder(COUNTERPART_PLACEHOLDER_HASH))
val record = a_lock_record_with(COUNTERPART_PLACEHOLDER_HASH)
assert_true(lock_record_has_placeholder(record))
val resolved = resolve_provider(a_wellformed_descriptor(), [record], "anything-at-all")
step("Confirm the state is UNVERIFIED, distinct from both verified and mismatched")
expect(verification_state_name(resolved.verification)).to_equal("unverified_placeholder")
assert_false(verification_state_is_verified(resolved.verification))
step("Confirm a placeholder cannot masquerade as a checked hash even when the observed digest equals it")
val echoed = resolve_provider(
    a_wellformed_descriptor(),
    [record],
    COUNTERPART_PLACEHOLDER_HASH
)
expect(verification_state_name(echoed.verification)).to_equal("unverified_placeholder")
assert_false(resolved_provider_is_usable(echoed))
```

</details>

#### refuses a descriptor whose abi_version is not the frozen one

- refuses a descriptor whose abi_version is not the frozen one
- Parse a descriptor pinned to the wrong ABI
   - Expected: descriptor.abi_version equals `2`
- Resolve it against an otherwise valid lock record
- Confirm the manifest is rejected before any hash is consulted
   - Expected: provider_status_name(resolved.status) equals `rejected_manifest`
   - Expected: verification_state_name(resolved.verification) equals `descriptor_rejected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("refuses a descriptor whose abi_version is not the frozen one")
step("Parse a descriptor pinned to the wrong ABI")
val descriptor = a_descriptor_with("abi_version: 1", "abi_version: 2")
expect(descriptor.abi_version).to_equal(2)
step("Resolve it against an otherwise valid lock record")
val resolved = resolve_provider(
    descriptor,
    [a_lock_record_with(VERIFIED_HASH)],
    VERIFIED_HASH
)
step("Confirm the manifest is rejected before any hash is consulted")
expect(provider_status_name(resolved.status)).to_equal("rejected_manifest")
expect(verification_state_name(resolved.verification)).to_equal("descriptor_rejected")
assert_false(resolved_provider_is_usable(resolved))
```

</details>

#### refuses a descriptor that declares no license

- refuses a descriptor that declares no license
- Parse a descriptor with its SPDX identifier removed
   - Expected: descriptor.license_spdx equals ``
- Confirm the frozen contract rejects it
- Confirm resolution refuses it rather than loading an unlicensed artifact
   - Expected: provider_status_name(resolved.status) equals `rejected_manifest`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("refuses a descriptor that declares no license")
step("Parse a descriptor with its SPDX identifier removed")
val descriptor = a_descriptor_with("  license_spdx: Apache-2.0\n", "")
expect(descriptor.license_spdx).to_equal("")
step("Confirm the frozen contract rejects it")
expect(descriptor_rejections(descriptor, VERIFIED_HASH).len()).to_be_greater_than(0)
step("Confirm resolution refuses it rather than loading an unlicensed artifact")
val resolved = resolve_provider(descriptor, [a_lock_record_with(VERIFIED_HASH)], VERIFIED_HASH)
expect(provider_status_name(resolved.status)).to_equal("rejected_manifest")
assert_false(resolved_provider_is_usable(resolved))
```

</details>

#### refuses a component whose boundary id is malformed

- refuses a component whose boundary id is malformed
- Parse a descriptor whose component boundary id has no schema version
   - Expected: descriptor.components[0].counterpart_boundary_id equals `mock.execution.echo`
- Confirm resolution rejects the manifest and names the component
   - Expected: provider_status_name(resolved.status) equals `rejected_manifest`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("refuses a component whose boundary id is malformed")
step("Parse a descriptor whose component boundary id has no schema version")
val descriptor = a_descriptor_with("mock.execution.echo@1", "mock.execution.echo")
expect(descriptor.components[0].counterpart_boundary_id).to_equal("mock.execution.echo")
step("Confirm resolution rejects the manifest and names the component")
val resolved = resolve_provider(descriptor, [a_lock_record_with(VERIFIED_HASH)], VERIFIED_HASH)
expect(provider_status_name(resolved.status)).to_equal("rejected_manifest")
assert_false(resolved_provider_is_usable(resolved))
expect(resolved.reasons.len()).to_be_greater_than(0)
```

</details>

#### reports an absent artifact as unavailable rather than as a mismatch

- reports an absent artifact as unavailable rather than as a mismatch
- Resolve with no artifact present on disk
- Confirm the missing artifact is named as missing
   - Expected: verification_state_name(resolved.verification) equals `artifact_missing`
   - Expected: provider_status_name(resolved.status) equals `unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("reports an absent artifact as unavailable rather than as a mismatch")
step("Resolve with no artifact present on disk")
val resolved = resolve_provider(a_wellformed_descriptor(), [a_lock_record_with(VERIFIED_HASH)], "")
step("Confirm the missing artifact is named as missing")
expect(verification_state_name(resolved.verification)).to_equal("artifact_missing")
expect(provider_status_name(resolved.status)).to_equal("unavailable")
assert_false(resolved_provider_is_usable(resolved))
```

</details>

#### refuses a lock record that omits the target triple

- refuses a lock record that omits the target triple
- Blank the target triple on an otherwise valid record
- Confirm the record is rejected with a stated reason
   - Expected: provider_status_name(resolved.status) equals `rejected_manifest`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("refuses a lock record that omits the target triple")
step("Blank the target triple on an otherwise valid record")
var record = a_lock_record_with(VERIFIED_HASH)
record.target_triple = ""
step("Confirm the record is rejected with a stated reason")
expect(lock_record_rejections(record).len()).to_be_greater_than(0)
val resolved = resolve_provider(a_wellformed_descriptor(), [record], VERIFIED_HASH)
expect(provider_status_name(resolved.status)).to_equal("rejected_manifest")
```

</details>

#### refuses a lock record whose license disagrees with the descriptor

- refuses a lock record whose license disagrees with the descriptor
- Set a different SPDX identifier on the lock record
- Confirm the disagreement is refused rather than resolved to one side
   - Expected: provider_status_name(resolved.status) equals `rejected_manifest`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("refuses a lock record whose license disagrees with the descriptor")
step("Set a different SPDX identifier on the lock record")
var record = a_lock_record_with(VERIFIED_HASH)
record.license_spdx = "GPL-3.0-only"
step("Confirm the disagreement is refused rather than resolved to one side")
val resolved = resolve_provider(a_wellformed_descriptor(), [record], VERIFIED_HASH)
expect(provider_status_name(resolved.status)).to_equal("rejected_manifest")
assert_false(resolved_provider_is_usable(resolved))
```

</details>

### Counterpart fetch guard

#### refuses to fetch a floating revision

- refuses to fetch a floating revision
- Pin the lock record to 'latest'
- Confirm fetch refuses it by name


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("refuses to fetch a floating revision")
step("Pin the lock record to 'latest'")
var record = a_lock_record_with(VERIFIED_HASH)
record.upstream_url = "https://example.invalid/upstream.git"
record.upstream_revision = "latest"
record.source_archive_sha256 = "abc123"
step("Confirm fetch refuses it by name")
expect(fetch_rejections(record).len()).to_be_greater_than(0)
```

</details>

#### refuses to fetch a record with no pinned revision at all

- refuses to fetch a record with no pinned revision at all
- Leave the upstream revision empty
- Confirm fetch refuses rather than defaulting to a branch head


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("refuses to fetch a record with no pinned revision at all")
step("Leave the upstream revision empty")
var record = a_lock_record_with(VERIFIED_HASH)
record.upstream_url = "https://example.invalid/upstream.git"
record.source_archive_sha256 = "abc123"
step("Confirm fetch refuses rather than defaulting to a branch head")
expect(fetch_rejections(record).len()).to_be_greater_than(0)
```

</details>

#### accepts a fully pinned upstream record

- accepts a fully pinned upstream record
- Pin an immutable revision and the archive hash to check it against
- Confirm the fetch guard raises no objection
   - Expected: fetch_rejections(record).len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("accepts a fully pinned upstream record")
step("Pin an immutable revision and the archive hash to check it against")
var record = a_lock_record_with(VERIFIED_HASH)
record.upstream_url = "https://example.invalid/upstream.git"
record.upstream_revision = "0b5f1c9a2d3e4f5061728394a5b6c7d8e9f00112"
record.source_archive_sha256 = "6d1e2f3a4b5c6d7e8f90a1b2c3d4e5f60718293a4b5c6d7e8f90a1b2c3d4e5f6"
step("Confirm the fetch guard raises no objection")
expect(fetch_rejections(record).len()).to_equal(0)
```

</details>

#### reports a missing artifact as no hash rather than as the empty-string digest

- reports a missing artifact as no hash rather than as the empty-string digest
- Hash an artifact path that does not exist
- Confirm the answer is empty, not sha256("")
   - Expected: digest equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("reports a missing artifact as no hash rather than as the empty-string digest")
step("Hash an artifact path that does not exist")
val digest = artifact_sha256_of_file("build/counterparts/does-not-exist/nothing.so")
step("Confirm the answer is empty, not sha256(\"\")")
expect(digest).to_equal("")
expect(digest).to_not_equal(
    "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
```

</details>

#### looks a lock record up by provider id and misses cleanly

- looks a lock record up by provider id and misses cleanly
- Look up a provider the lockfile does not carry
- Confirm the miss is nil rather than an arbitrary neighbouring record


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("looks a lock record up by provider id and misses cleanly")
step("Look up a provider the lockfile does not carry")
val absent = lock_record_for([a_lock_record_with(VERIFIED_HASH)], "harfbuzz")
step("Confirm the miss is nil rather than an arbitrary neighbouring record")
assert_nil(absent)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/infra/counterpart/counterpart_conformance_parallel_agent_plan_2026-08-09.md`
- **Design:** `doc/05_design/infra/counterpart/counterpart_conformance_infrastructure_design_2026-08-09.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INFRA`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c914bec119cac0fc1cee75952de0093cdc22b016adca7f10214d76fa7c649b94`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c914bec119cac0fc1cee75952de0093cdc22b016adca7f10214d76fa7c649b94`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c914bec119cac0fc1cee75952de0093cdc22b016adca7f10214d76fa7c649b94`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/infra/counterpart/package_registry_spec.spl
mirror: doc/06_spec/01_unit/infra/counterpart/package_registry_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=100
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
test/01_unit/infra/counterpart/package_registry_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/infra/counterpart/package_registry_spec.spl:167:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads a provider descriptor including its component list' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/infra/counterpart/package_registry_spec.spl:186:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads a deliberately empty lock field without ending the record' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/infra/counterpart/package_registry_spec.spl:204:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'addresses the cache by target and build digest' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
