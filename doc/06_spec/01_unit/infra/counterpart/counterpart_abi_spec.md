# Counterpart Provider Adapter ABI (v1)

> Every counterpart conformance provider — a zstd wrapper, a Chrome driver, a

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Counterpart Provider Adapter ABI (v1)

Every counterpart conformance provider — a zstd wrapper, a Chrome driver, a

## At a Glance

| Field | Value |
|-------|-------|
| Category | Infrastructure |
| Status | Active |
| Plan | doc/03_plan/infra/counterpart/counterpart_conformance_parallel_agent_plan_2026-08-09.md |
| Design | doc/05_design/infra/counterpart/counterpart_conformance_infrastructure_design_2026-08-09.md |
| Source | `test/01_unit/infra/counterpart/counterpart_abi_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Every counterpart conformance provider — a zstd wrapper, a Chrome driver, a
Vulkan reference — is loaded through one stable C ABI, `scf_api_v1`. This
scenario is how an infrastructure engineer confirms that ABI actually holds:
that a wrong version is refused rather than misread, that a manifest describes
real components, that a deterministic component really is deterministic, and
that a component's failure arrives as structured evidence instead of silently
becoming a pass.

The subject under test is the mock adapter, which exists for exactly this
purpose: it has no upstream dependency, so a red result here is a defect in the
ABI, the runtime shim, or the Simple wrapper — never in a third-party library.

## Scope and Preconditions

The mock adapter must be built as a shared library at
`build/counterparts/libsimple_counterpart_mock.so`:

    cc -std=c99 -fPIC -shared -Itools/counterpart/sdk/c \\
       tools/counterpart/adapters/mock/simple_counterpart_mock.c \\
       -o build/counterparts/libsimple_counterpart_mock.so

When that library is absent, the provider is UNAVAILABLE and these scenarios
fail. They are never reported as passing, because a conformance framework that
green-lights a missing provider is the exact failure this infrastructure exists
to prevent.

## Primary Workflow

Negotiate ABI v1 against the adapter, read its manifest, invoke each component,
and read the response and trace envelopes it wrote through the caller-owned
writer. The adapter allocates nothing the caller must free, and no raw pointer
reaches Simple.

## Key Concepts

| Concept | Description |
|---------|-------------|
| `scf_get_api` | The single bootstrap symbol every adapter exports |
| ABI negotiation | `scf_get_api(v)` returns NULL for an unsupported `v` |
| Response envelope | SDN text carrying the component's result, error included |
| Trace envelope | SDN text carrying how the invocation was executed |
| Structured error | A failure expressed as data, not as an overloaded nonzero return |

## Related Specifications

- [Frozen counterpart contracts](../../../../src/lib/common/spec/evidence/counterpart/model.spl) — ProviderStatus and manifest records

## Evidence and Provenance

Evidence is the live adapter: manifest text, response envelopes and digests are
read from a real dlopen'd library at run time, not from a fixture.

## Recovery and Troubleshooting

`library_not_loadable` means the shared library is missing — build it with the
command above. `abi_version_mismatch` or `adapter_refused_abi` means the adapter
was built against a different ABI revision; rebuild it against
`tools/counterpart/sdk/c/simple_counterpart_abi.h`.

## Compatibility and Limitations

The `mock.crash` component deliberately `abort()`s and is therefore NOT invoked
here: in-process loading cannot contain a crashing adapter. Proving that a crash
is reported as `provider_status: crashed` belongs to the isolated worker (F3),
which runs the adapter in a separate process. This spec covers the in-process
lane only, and says so rather than pretending the crash path is covered.

## Scenarios

### Counterpart provider adapter ABI v1

#### refuses a version it does not implement and accepts the one it does

- refuses a version it does not implement and accepts the one it does
- Ask the adapter whether it serves ABI version 1
- Ask the same adapter for ABI version 2, which does not exist
- Confirm negotiation against a nonexistent library reports unavailable, not served


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("refuses a version it does not implement and accepts the one it does")
step("Ask the adapter whether it serves ABI version 1")
val serves_v1 = CounterpartLibrary.serves_abi(MOCK_ADAPTER_PATH, 1)
match serves_v1:
    Ok(served) => assert_true(served)
    Err(failure) => fail("ABI probe failed: " + failure.status_name)

step("Ask the same adapter for ABI version 2, which does not exist")
val serves_v2 = CounterpartLibrary.serves_abi(MOCK_ADAPTER_PATH, 2)
match serves_v2:
    Ok(served) => assert_false(served)
    Err(failure) => fail("ABI probe failed: " + failure.status_name)

step("Confirm negotiation against a nonexistent library reports unavailable, not served")
val missing = CounterpartLibrary.serves_abi("build/counterparts/libno_such_provider.so", 1)
match missing:
    Ok(served) => fail("a nonexistent library reported served=" + served.to_text())
    Err(failure) => expect(failure.status_name).to_equal("library_not_loadable")
```

</details>

#### publishes a manifest naming its provider and every component

- publishes a manifest naming its provider and every component
- Open the mock adapter
- Read the provider manifest
- Verify the manifest identifies the provider and its independence group
   - Expected: counterpart_manifest_field(manifest, "provider_id") equals `mock`
   - Expected: counterpart_manifest_field(manifest, "independence_group") equals `mock`
   - Expected: counterpart_manifest_field(manifest, "abi_version") equals `1`
- Verify all four declared components are present
   - Expected: components.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("publishes a manifest naming its provider and every component")
step("Open the mock adapter")
var library = open_mock_adapter()

step("Read the provider manifest")
val manifest = read_manifest(library)

step("Verify the manifest identifies the provider and its independence group")
expect(counterpart_manifest_field(manifest, "provider_id")).to_equal("mock")
expect(counterpart_manifest_field(manifest, "independence_group")).to_equal("mock")
expect(counterpart_manifest_field(manifest, "abi_version")).to_equal("1")

step("Verify all four declared components are present")
val components = counterpart_manifest_component_ids(manifest)
expect(components.len()).to_equal(4)
expect(components).to_contain("mock.echo")
expect(components).to_contain("mock.hash")
expect(components).to_contain("mock.error")
expect(components).to_contain("mock.crash")

library.close()
```

</details>

#### round-trips a request through mock.echo unchanged

- round-trips a request through mock.echo unchanged
- Open the mock adapter
- Send a request containing a quote, which the envelope must escape
- Verify the response reports ok and carries the request back verbatim
   - Expected: counterpart_manifest_field(envelope, "status") equals `ok`
   - Expected: counterpart_manifest_field(envelope, "schema_id") equals `mock.echo_response@1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("round-trips a request through mock.echo unchanged")
step("Open the mock adapter")
var library = open_mock_adapter()

step("Send a request containing a quote, which the envelope must escape")
val envelope = invoke_component(library, "mock.echo", "counterpart \"probe\"")

step("Verify the response reports ok and carries the request back verbatim")
expect(counterpart_manifest_field(envelope, "status")).to_equal("ok")
expect(counterpart_manifest_field(envelope, "schema_id")).to_equal("mock.echo_response@1")
expect(envelope).to_contain("counterpart \\\"probe\\\"")

library.close()
```

</details>

#### produces the same mock.hash digest for the same input twice

- produces the same mock.hash digest for the same input twice
- Open the mock adapter
- Hash the same input on two separate invocations
- Verify both invocations produced a non-empty digest
   - Expected: first.len() equals `16`
   - Expected: second.len() equals `16`
- Verify the two digests are identical
   - Expected: first equals `second`
- Verify a different input produces a different digest, so equality is not vacuous


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("produces the same mock.hash digest for the same input twice")
step("Open the mock adapter")
var library = open_mock_adapter()

step("Hash the same input on two separate invocations")
val first = digest_of(invoke_component(library, "mock.hash", "deterministic-input"))
val second = digest_of(invoke_component(library, "mock.hash", "deterministic-input"))

step("Verify both invocations produced a non-empty digest")
expect(first.len()).to_equal(16)
expect(second.len()).to_equal(16)

step("Verify the two digests are identical")
expect(first).to_equal(second)

step("Verify a different input produces a different digest, so equality is not vacuous")
val other = digest_of(invoke_component(library, "mock.hash", "other-input"))
assert_not_equal(first, other)

library.close()
```

</details>

#### reports a mock.error failure as a structured envelope, never as a pass

- reports a mock.error failure as a structured envelope, never as a pass
- Open the mock adapter
- Invoke the component that always fails by contract
- Verify the ABI call itself succeeded — the failure is carried as data
- Verify the envelope declares an error status with a machine-readable code
   - Expected: counterpart_manifest_field(response.response, "status") equals `error`
   - Expected: counterpart_manifest_field(response.response, "item_count") equals `0`
- Verify the failure is not mistakable for a successful component


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("reports a mock.error failure as a structured envelope, never as a pass")
step("Open the mock adapter")
var library = open_mock_adapter()

step("Invoke the component that always fails by contract")
val outcome = library.invoke("mock.error", "any-request")

step("Verify the ABI call itself succeeded — the failure is carried as data")
match outcome:
    Ok(response) =>
        step("Verify the envelope declares an error status with a machine-readable code")
        expect(counterpart_manifest_field(response.response, "status")).to_equal("error")
        expect(counterpart_manifest_field(response.response, "error_code"))
            .to_equal("mock.deliberate_failure")
        expect(counterpart_manifest_field(response.response, "item_count")).to_equal("0")
        step("Verify the failure is not mistakable for a successful component")
        assert_not_equal(counterpart_manifest_field(response.response, "status"), "ok")
    Err(failure) =>
        fail("mock.error returned a bare status " + failure.status_name
            + " instead of a structured error envelope")

library.close()
```

</details>

### Counterpart provider adapter ABI v1 edge cases

#### rejects an unknown component instead of returning an empty success

- rejects an unknown component instead of returning an empty success
- Open the mock adapter
- Invoke a component the manifest does not declare
- Verify the call is refused with unknown_component


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("rejects an unknown component instead of returning an empty success")
step("Open the mock adapter")
var library = open_mock_adapter()

step("Invoke a component the manifest does not declare")
val outcome = library.invoke("mock.not_declared", "x")

step("Verify the call is refused with unknown_component")
match outcome:
    Ok(response) => fail("undeclared component returned a response: " + response.response)
    Err(failure) => expect(failure.status_name).to_equal("unknown_component")

library.close()
```

</details>

#### refuses every call once the library has been closed

- refuses every call once the library has been closed
- Open and immediately close the mock adapter
- Verify the handle is no longer live
- Verify a further invoke is refused rather than silently ignored


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("refuses every call once the library has been closed")
step("Open and immediately close the mock adapter")
var library = open_mock_adapter()
library.close()

step("Verify the handle is no longer live")
assert_false(library.is_open())

step("Verify a further invoke is refused rather than silently ignored")
match library.invoke("mock.echo", "x"):
    Ok(response) => fail("closed library served a request: " + response.response)
    Err(failure) => expect(failure.status_name).to_equal("bad_handle")
```

</details>

#### names every status code it can report

- names every status code it can report
- Verify each ABI status maps to a stable diagnostic name
   - Expected: counterpart_status_text(0) equals `ok`
   - Expected: counterpart_status_text(2) equals `unknown_component`
   - Expected: counterpart_status_text(3) equals `schema_mismatch`
   - Expected: counterpart_status_text(-5) equals `abi_version_mismatch`
   - Expected: counterpart_status_text(-9) equals `bad_handle`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INFRA
step("names every status code it can report")
step("Verify each ABI status maps to a stable diagnostic name")
expect(counterpart_status_text(0)).to_equal("ok")
expect(counterpart_status_text(2)).to_equal("unknown_component")
expect(counterpart_status_text(3)).to_equal("schema_mismatch")
expect(counterpart_status_text(-5)).to_equal("abi_version_mismatch")
expect(counterpart_status_text(-9)).to_equal("bad_handle")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- `REQ-SSPEC-UNIT`
- `REQ-COUNTERPART-ABI-001`
- `REQ-SSPEC-INFRA`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5a3bb56bc24cdf31da1a3d0fffd45544c5c30f4a817859fd135e936b4139c9be`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5a3bb56bc24cdf31da1a3d0fffd45544c5c30f4a817859fd135e936b4139c9be`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5a3bb56bc24cdf31da1a3d0fffd45544c5c30f4a817859fd135e936b4139c9be`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/infra/counterpart/counterpart_abi_spec.spl
mirror: doc/06_spec/01_unit/infra/counterpart/counterpart_abi_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=90
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/infra/counterpart/counterpart_abi_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/01_unit/infra/counterpart/counterpart_abi_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/infra/counterpart/counterpart_abi_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/infra/counterpart/counterpart_abi_spec.spl:137:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'refuses a version it does not implement and accepts the one it does' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/infra/counterpart/counterpart_abi_spec.spl:158:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'publishes a manifest naming its provider and every component' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/infra/counterpart/counterpart_abi_spec.spl:182:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips a request through mock.echo unchanged' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
