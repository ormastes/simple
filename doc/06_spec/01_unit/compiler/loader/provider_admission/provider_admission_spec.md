# Provider Admission Specification

> Tests covering metadata-only provider admission.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Provider Admission Specification

## Scenarios

### metadata-only provider admission

#### should keep reserved finalization unpublished and reject competing writers

_Requirements: `REQ-002 REQ-012`_

- Reserve finalization while the provider remains admitting
   - Expected: provider_admission_state_v1(admission) equals `ProviderAdmissionStateV1.admitting`
- Refuse both competing terminal writers without publishing metadata


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reserve finalization while the provider remains admitting")
val admission = terminal_state_fixture()
expect(provider_admission_try_claim_v1(admission)).to_be(true)
expect(admission.atomic_state.compare_exchange(1, 3, MemoryOrdering.AcqRel, MemoryOrdering.Acquire)).to_be(true)
expect(provider_admission_state_v1(admission)).to_equal(ProviderAdmissionStateV1.admitting)
step("Refuse both competing terminal writers without publishing metadata")
expect(provider_admission_publish_v1(admission, terminal_state_receipt("competitor"))).to_be(false)
expect(provider_admission_reject_v1(admission, ProviderAdmissionErrorV1.abi_mismatch)).to_be(false)
expect(admission.receipt).to_be_nil()
expect(admission.failure).to_be_nil()
```

</details>

#### should preserve the first receipt after refusing duplicate publication

_Requirements: `REQ-002 REQ-012`_

- Claim admission and publish the primary receipt
- Refuse replacement and retain the admitted identity
   - Expected: admission.receipt.unwrap().provider_identity equals `primary`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Claim admission and publish the primary receipt")
val admission = terminal_state_fixture()
expect(provider_admission_try_claim_v1(admission)).to_be(true)
expect(provider_admission_publish_v1(admission, terminal_state_receipt("primary"))).to_be(true)
step("Refuse replacement and retain the admitted identity")
expect(provider_admission_publish_v1(admission, terminal_state_receipt("replacement"))).to_be(false)
expect(admission.receipt.unwrap().provider_identity).to_equal("primary")
```

</details>

#### should preserve rejection without attaching a later receipt

_Requirements: `REQ-002 REQ-012`_

- Reject the claimed admission with its typed failure
- Refuse publication after rejection
   - Expected: admission.failure.unwrap().error equals `ProviderAdmissionErrorV1.abi_mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject the claimed admission with its typed failure")
val admission = terminal_state_fixture()
expect(provider_admission_try_claim_v1(admission)).to_be(true)
expect(provider_admission_reject_v1(admission, ProviderAdmissionErrorV1.abi_mismatch)).to_be(true)
step("Refuse publication after rejection")
expect(provider_admission_publish_v1(admission, terminal_state_receipt("primary"))).to_be(false)
expect(admission.receipt).to_be_nil()
expect(admission.failure.unwrap().error).to_equal(ProviderAdmissionErrorV1.abi_mismatch)
```

</details>

#### should preserve admission without attaching a later failure

_Requirements: `REQ-002 REQ-012`_

- Publish the claimed admission
- Refuse rejection after publication
   - Expected: provider_admission_state_v1(admission) equals `ProviderAdmissionStateV1.admitted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Publish the claimed admission")
val admission = terminal_state_fixture()
expect(provider_admission_try_claim_v1(admission)).to_be(true)
expect(provider_admission_publish_v1(admission, terminal_state_receipt("primary"))).to_be(true)
step("Refuse rejection after publication")
expect(provider_admission_reject_v1(admission, ProviderAdmissionErrorV1.abi_mismatch)).to_be(false)
expect(admission.failure).to_be_nil()
expect(provider_admission_state_v1(admission)).to_equal(ProviderAdmissionStateV1.admitted)
```

</details>

#### admits one effect owner and keeps the shadow metadata-only

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val descriptor = ProviderDescriptorV1(
    "pure.provider", "pkg.provider", sha256_text("abi"),
    [sha256_text("dependency")], ProviderModeV1.shadow_compare,
    "foreign.provider", true)
val policy = provider_admission_policy_v1(descriptor)
expect(policy.is_ok()).to_equal(true)
expect(policy.unwrap().effect_owner_identity).to_equal("pure.provider")
expect(policy.unwrap().shadow_metadata_only).to_equal(true)
```

</details>

#### rejects a dual mode policy with the same primary and shadow

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val descriptor = ProviderDescriptorV1(
    "same.provider", "pkg.provider", sha256_text("abi"), [],
    ProviderModeV1.shadow_compare, "same.provider", true)
expect(provider_admission_policy_v1(descriptor).is_err()).to_equal(true)
```

</details>

#### issues an execution ticket only to the admitted effect owner

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = ProviderEffectPolicyV1("pure.provider", true)
val receipt = ProviderAdmissionReceiptV1(
    "pure.provider", "pkg.provider", sha256_text("archive"),
    sha256_text("receipt"), sha256_text("abi"), [],
    ProviderModeV1.shadow_compare, policy, true, false)
val ticket = provider_execution_ticket_v1(receipt)
expect(ticket.is_ok()).to_equal(true)
expect(ticket.unwrap().effect_owner_identity).to_equal("pure.provider")
```

</details>

#### uses one atomic owner and caches typed rejection

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = read_file(STATE_PATH)
val admission = read_file(ADMISSION_PATH)
expect(state).to_contain("atomic_state.compare_exchange(")
expect(state).to_contain("ProviderAdmissionFailureV1?")
expect(admission).to_contain("cached_rejection")
expect(admission).to_contain("PROVIDER_ADMISSION_WAIT_BUDGET_V1")
expect(admission).to_contain("thread_yield()")
```

</details>

#### binds package image receipt and pinned capability authority

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val admission = read_file(ADMISSION_PATH)
expect(admission).to_contain("package_image_validate_v1(")
expect(admission).to_contain("authority.capability.archive_digest")
expect(admission).to_contain("authority.capability.receipt_digest")
expect(admission).to_contain("authority.capability.identity.content_digest")
expect(admission).to_contain("package_identity_mismatch")
expect(admission).to_contain("dependency_mismatch")
```

</details>

#### keeps admission metadata-only

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val admission = read_file(ADMISSION_PATH)
expect(admission.contains("pinned_archive_read_member_v1")).to_equal(false)
expect(admission.contains("read_file(")).to_equal(false)
expect(admission.contains("rt_process_run")).to_equal(false)
expect(admission.contains("provider_execute")).to_equal(false)
expect(admission.contains("provider_initialize")).to_equal(false)
```

</details>

#### permits only the primary provider to own effects in dual mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = read_file(STATE_PATH)
val admission = read_file(ADMISSION_PATH)
expect(state).to_contain("shadow_metadata_only: bool")
expect(state).to_contain("effect_owner_identity: text")
expect(admission).to_contain("descriptor.provider_identity, true")
expect(state).to_contain(
    "receipt.effect_policy.effect_owner_identity != receipt.provider_identity")
```

</details>

#### separates execution authority from admission authority

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = read_file(STATE_PATH)
expect(state).to_contain("ProviderExecutionTicketV1")
expect(state).to_contain("fn provider_execution_ticket_v1(")
expect(state).to_contain("invalid_dual_mode_policy")
```

</details>

#### has typed rejection for malformed and incompatible authority

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = read_file(STATE_PATH)
for error in [
        "invalid_descriptor", "invalid_package_image",
        "invalid_archive_capability", "package_identity_mismatch",
        "abi_mismatch", "dependency_mismatch",
        "invalid_dual_mode_policy", "admission_conflict",
        "wait_exhausted", "cached_rejection"]:
    expect(state).to_contain(error)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/loader/provider_admission/provider_admission_spec.spl` |
| Updated | 2026-09-29 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering metadata-only provider admission.
- metadata-only provider admission

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
