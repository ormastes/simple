# Domain Arena V1 Specification

> Tests covering sealed relaxed-allocation domain arena v1.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Domain Arena V1 Specification

## Scenarios

### sealed relaxed-allocation domain arena v1

#### uses a canonical SHA-256 identity for the sealed profile

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses a canonical SHA-256 identity for the sealed profile
   - Expected: fingerprint.len() equals `64`
   - Expected: fingerprint equals `relaxed_allocation_profile_hash_v1(profile)`
   - Expected: fingerprint equals `a77be0b0e329204db951474c0085526c103049d51ce6ae6a194e5f9312bd11b3`
   - Expected: relaxed_allocation_profile_hash_v1(relaxed_test_profile_v1(65u64)) == fingerprint is false
   - Expected: relaxed_allocation_profile_hash_v1(delimiter_profile) == fingerprint is false
   - Expected: relaxed_allocation_profile_hash_v1(field_profile) == fingerprint is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("uses a canonical SHA-256 identity for the sealed profile")
val profile = relaxed_test_profile_v1(64u64)
val fingerprint = relaxed_allocation_profile_fingerprint_v1(profile)
expect(fingerprint.len()).to_equal(64)
expect(fingerprint).to_equal(relaxed_allocation_profile_hash_v1(profile))
expect(fingerprint).to_equal("a77be0b0e329204db951474c0085526c103049d51ce6ae6a194e5f9312bd11b3")
expect(relaxed_allocation_profile_hash_v1(relaxed_test_profile_v1(65u64)) == fingerprint).to_equal(false)
var delimiter_profile = relaxed_test_profile_v1(64u64)
delimiter_profile.profile_id = "render|domain:µ"
val framed = relaxed_allocation_profile_canonical_v1(delimiter_profile)
expect(framed).to_contain("profile_id=16:render|domain:µ")
expect(relaxed_allocation_profile_hash_v1(delimiter_profile) == fingerprint).to_equal(false)
var field_profile = relaxed_test_profile_v1(64u64)
field_profile.alignment = 16u32
expect(relaxed_allocation_profile_hash_v1(field_profile) == fingerprint).to_equal(false)
```

</details>

#### enumerates the complete named failure-point registry

- enumerates the complete named failure-point registry
   - Expected: arena_failure_point_count_v1() equals `2u16`
   - Expected: arena_failure_point_at_v1(0u16) equals `ARENA_FAULT_BEFORE_CURSOR_ADVANCE`
   - Expected: arena_failure_point_at_v1(1u16) equals `ARENA_FAULT_BEFORE_PUBLICATION`
   - Expected: arena_failure_point_at_v1(2u16) equals `ARENA_FAULT_NONE`
   - Expected: arena_failure_point_name_v1(ARENA_FAULT_BEFORE_CURSOR_ADVANCE) equals `before_cursor_advance`
   - Expected: arena_failure_point_name_v1(ARENA_FAULT_BEFORE_PUBLICATION) equals `before_publication`
   - Expected: arena_failure_point_registered_v1(99u16) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("enumerates the complete named failure-point registry")
expect(arena_failure_point_count_v1()).to_equal(2u16)
expect(arena_failure_point_at_v1(0u16)).to_equal(ARENA_FAULT_BEFORE_CURSOR_ADVANCE)
expect(arena_failure_point_at_v1(1u16)).to_equal(ARENA_FAULT_BEFORE_PUBLICATION)
expect(arena_failure_point_at_v1(2u16)).to_equal(ARENA_FAULT_NONE)
expect(arena_failure_point_name_v1(ARENA_FAULT_BEFORE_CURSOR_ADVANCE)).to_equal("before_cursor_advance")
expect(arena_failure_point_name_v1(ARENA_FAULT_BEFORE_PUBLICATION)).to_equal("before_publication")
expect(arena_failure_point_registered_v1(99u16)).to_equal(false)
```

</details>

#### binds every profile and committed-snapshot field into its hash

- binds every profile and committed-snapshot field into its hash
   - Expected: relaxed_allocation_profile_hash_v1(changed) == base_hash is false
   - Expected: relaxed_allocation_profile_hash_v1(changed) == base_hash is false
   - Expected: relaxed_allocation_profile_hash_v1(changed) == base_hash is false
   - Expected: relaxed_allocation_profile_hash_v1(changed) == base_hash is false
   - Expected: relaxed_allocation_profile_hash_v1(changed) == base_hash is false
   - Expected: relaxed_allocation_profile_hash_v1(changed) == base_hash is false
   - Expected: relaxed_allocation_profile_hash_v1(changed) == base_hash is false
   - Expected: relaxed_allocation_profile_hash_v1(changed) == base_hash is false
   - Expected: relaxed_allocation_profile_hash_v1(changed) == base_hash is false
   - Expected: relaxed_allocation_profile_hash_v1(changed) == base_hash is false
   - Expected: arena.commit(checkpoint) is true
   - Expected: domain_arena_committed_state_hash_v1(arena) == committed_hash is false
   - Expected: domain_arena_committed_state_hash_v1(arena) == committed_hash is false
   - Expected: domain_arena_committed_state_hash_v1(arena) == committed_hash is false
   - Expected: domain_arena_committed_state_hash_v1(arena) == committed_hash is false
   - Expected: domain_arena_committed_state_hash_v1(arena) == committed_hash is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 54 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("binds every profile and committed-snapshot field into its hash")
val base_profile = relaxed_test_profile_v1(64u64)
val base_hash = relaxed_allocation_profile_hash_v1(base_profile)
var changed = base_profile
changed.schema_version = 2u16
expect(relaxed_allocation_profile_hash_v1(changed) == base_hash).to_equal(false)
changed = base_profile
changed.profile_id = "other"
expect(relaxed_allocation_profile_hash_v1(changed) == base_hash).to_equal(false)
changed = base_profile
changed.strict_default = false
expect(relaxed_allocation_profile_hash_v1(changed) == base_hash).to_equal(false)
changed = base_profile
changed.domain_id = 5u32
expect(relaxed_allocation_profile_hash_v1(changed) == base_hash).to_equal(false)
changed = base_profile
changed.quota_bytes = 65u64
expect(relaxed_allocation_profile_hash_v1(changed) == base_hash).to_equal(false)
changed = base_profile
changed.alignment = 16u32
expect(relaxed_allocation_profile_hash_v1(changed) == base_hash).to_equal(false)
changed = base_profile
changed.max_allocations_per_generation = 3u32
expect(relaxed_allocation_profile_hash_v1(changed) == base_hash).to_equal(false)
changed = base_profile
changed.allowed_context_mask = 3u64
expect(relaxed_allocation_profile_hash_v1(changed) == base_hash).to_equal(false)
changed = base_profile
changed.forbidden_context_mask = 60u64
expect(relaxed_allocation_profile_hash_v1(changed) == base_hash).to_equal(false)
changed = base_profile
changed.sealed = false
expect(relaxed_allocation_profile_hash_v1(changed) == base_hash).to_equal(false)

val arena = DomainArenaV1.from_sealed_profile(77u64, base_profile)
val checkpoint = arena.checkpoint()
arena.try_allocate(8u64, ARENA_CONTEXT_NORMAL)
expect(arena.commit(checkpoint)).to_equal(true)
val committed_hash = domain_arena_committed_state_hash_v1(arena)
arena.committed_state.generation = 2u64
expect(domain_arena_committed_state_hash_v1(arena) == committed_hash).to_equal(false)
arena.committed_state.generation = 1u64
arena.committed_state.cursor_bytes = 16u64
expect(domain_arena_committed_state_hash_v1(arena) == committed_hash).to_equal(false)
arena.committed_state.cursor_bytes = 8u64
arena.committed_state.allocation_count = 2u32
expect(domain_arena_committed_state_hash_v1(arena) == committed_hash).to_equal(false)
arena.committed_state.allocation_count = 1u32
arena.committed_state.publication_epoch = 2u64
expect(domain_arena_committed_state_hash_v1(arena) == committed_hash).to_equal(false)
arena.committed_state.publication_epoch = 1u64
arena.profile.domain_id = 5u32
expect(domain_arena_committed_state_hash_v1(arena) == committed_hash).to_equal(false)
```

</details>

#### ignores compatibility mirror tampering in operational paths

- ignores compatibility mirror tampering in operational paths
   - Expected: arena.commit(first) is true
   - Expected: second.publication_epoch equals `1u64`
   - Expected: arena.rollback(second) is true
   - Expected: arena.cursor_bytes equals `8u64`
   - Expected: arena.generation equals `1u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("ignores compatibility mirror tampering in operational paths")
val arena = DomainArenaV1.from_sealed_profile(78u64, relaxed_test_profile_v1(64u64))
val first = arena.checkpoint()
arena.try_allocate(8u64, ARENA_CONTEXT_NORMAL)
expect(arena.commit(first)).to_equal(true)
arena.committed_generation = 999u64
arena.committed_cursor_bytes = 63u64
arena.committed_allocation_count = 99u32
arena.publication_epoch = 999u64
val second = arena.checkpoint()
expect(second.publication_epoch).to_equal(1u64)
expect(arena.rollback(second)).to_equal(true)
expect(arena.cursor_bytes).to_equal(8u64)
expect(arena.generation).to_equal(1u64)
```

</details>

#### accepts exact quota and rejects plus one without cursor mutation

- accepts exact quota and rejects plus one without cursor mutation
   - Expected: exact is true
   - Expected: receipt.reason equals `ARENA_EXHAUSTION_QUOTA`
   - Expected: false is true
   - Expected: arena.cursor_bytes equals `64u64`
   - Expected: arena.rollback(checkpoint) is true
   - Expected: arena.cursor_bytes equals `0u64`
   - Expected: arena.allocation_count equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts exact quota and rejects plus one without cursor mutation")
val arena = DomainArenaV1.from_sealed_profile(11u64, relaxed_test_profile_v1(64u64))
val checkpoint = arena.checkpoint()
var exact = false
match arena.try_allocate(64u64, ARENA_CONTEXT_NORMAL):
    DomainArenaAllocationV1.Allocated(reference):
        exact = reference.offset_bytes == 0u64
    DomainArenaAllocationV1.Exhausted(receipt):
        exact = false
expect(exact).to_equal(true)
match arena.try_allocate(1u64, ARENA_CONTEXT_NORMAL):
    DomainArenaAllocationV1.Exhausted(receipt):
        expect(receipt.reason).to_equal(ARENA_EXHAUSTION_QUOTA)
    DomainArenaAllocationV1.Allocated(reference):
        expect(false).to_equal(true)
expect(arena.cursor_bytes).to_equal(64u64)
expect(arena.rollback(checkpoint)).to_equal(true)
expect(arena.cursor_bytes).to_equal(0u64)
expect(arena.allocation_count).to_equal(0u32)
```

</details>

#### rejects strict and forbidden contexts before mutation

- rejects strict and forbidden contexts before mutation
   - Expected: receipt.reason equals `ARENA_EXHAUSTION_UNSEALED`
   - Expected: false is true
   - Expected: strict_arena.cursor_bytes equals `0u64`
   - Expected: receipt.reason equals `ARENA_EXHAUSTION_FORBIDDEN_CONTEXT`
   - Expected: false is true
   - Expected: forbidden_arena.cursor_bytes equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects strict and forbidden contexts before mutation")
var unsealed = relaxed_test_profile_v1(64u64)
unsealed.sealed = false
val strict_arena = DomainArenaV1.from_sealed_profile(12u64, unsealed)
strict_arena.checkpoint()
match strict_arena.try_allocate(8u64, ARENA_CONTEXT_NORMAL):
    DomainArenaAllocationV1.Exhausted(receipt):
        expect(receipt.reason).to_equal(ARENA_EXHAUSTION_UNSEALED)
    DomainArenaAllocationV1.Allocated(reference):
        expect(false).to_equal(true)
expect(strict_arena.cursor_bytes).to_equal(0u64)

val forbidden_arena = DomainArenaV1.from_sealed_profile(13u64, relaxed_test_profile_v1(64u64))
forbidden_arena.checkpoint()
match forbidden_arena.try_allocate(8u64, ARENA_CONTEXT_ISR):
    DomainArenaAllocationV1.Exhausted(receipt):
        expect(receipt.reason).to_equal(ARENA_EXHAUSTION_FORBIDDEN_CONTEXT)
    DomainArenaAllocationV1.Allocated(reference):
        expect(false).to_equal(true)
expect(forbidden_arena.cursor_bytes).to_equal(0u64)
```

</details>

#### commits a transaction and invalidates rolled-back references

- commits a transaction and invalidates rolled-back references
   - Expected: false is true
   - Expected: arena.validates(allocated_ref) is false
   - Expected: arena.rollback(checkpoint) is true
   - Expected: arena.validates(allocated_ref) is false
   - Expected: arena.commit(committed) is true
   - Expected: arena.publication_epoch equals `1u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("commits a transaction and invalidates rolled-back references")
val arena = DomainArenaV1.from_sealed_profile(14u64, relaxed_test_profile_v1(64u64))
val checkpoint = arena.checkpoint()
var allocated_ref = DomainArenaRefV1(
    arena_id: 0u64, domain_id: 0u32, generation: 0u64,
    offset_bytes: 0u64, size_bytes: 0u64
)
match arena.try_allocate(8u64, ARENA_CONTEXT_NORMAL):
    DomainArenaAllocationV1.Allocated(reference):
        allocated_ref = reference
    DomainArenaAllocationV1.Exhausted(receipt):
        expect(false).to_equal(true)
# Staging references stay private until a successful commit.
expect(arena.validates(allocated_ref)).to_equal(false)
expect(arena.rollback(checkpoint)).to_equal(true)
expect(arena.validates(allocated_ref)).to_equal(false)

val committed = arena.checkpoint()
arena.try_allocate(8u64, ARENA_CONTEXT_NORMAL)
expect(arena.commit(committed)).to_equal(true)
expect(arena.publication_epoch).to_equal(1u64)
```

</details>

#### preserves the committed generation when a later staging generation rolls back

- preserves the committed generation when a later staging generation rolls back
   - Expected: false is true
   - Expected: arena.commit(first_checkpoint) is true
   - Expected: arena.validates(first_ref) is true
   - Expected: false is true
   - Expected: arena.rollback(second_checkpoint) is true
   - Expected: arena.validates(first_ref) is true
   - Expected: arena.validates(second_ref) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("preserves the committed generation when a later staging generation rolls back")
val arena = DomainArenaV1.from_sealed_profile(17u64, relaxed_test_profile_v1(64u64))
val first_checkpoint = arena.checkpoint()
var first_ref = DomainArenaRefV1(
    arena_id: 0u64, domain_id: 0u32, generation: 0u64,
    offset_bytes: 0u64, size_bytes: 0u64
)
match arena.try_allocate(8u64, ARENA_CONTEXT_NORMAL):
    DomainArenaAllocationV1.Allocated(reference):
        first_ref = reference
    DomainArenaAllocationV1.Exhausted(receipt):
        expect(false).to_equal(true)
expect(arena.commit(first_checkpoint)).to_equal(true)
expect(arena.validates(first_ref)).to_equal(true)

val second_checkpoint = arena.checkpoint()
var second_ref = DomainArenaRefV1(
    arena_id: 0u64, domain_id: 0u32, generation: 0u64,
    offset_bytes: 0u64, size_bytes: 0u64
)
match arena.try_allocate(16u64, ARENA_CONTEXT_NORMAL):
    DomainArenaAllocationV1.Allocated(reference):
        second_ref = reference
    DomainArenaAllocationV1.Exhausted(receipt):
        expect(false).to_equal(true)
expect(arena.rollback(second_checkpoint)).to_equal(true)
expect(arena.validates(first_ref)).to_equal(true)
expect(arena.validates(second_ref)).to_equal(false)
```

</details>

#### rejects forged checkpoints and keeps the original rollback point

- rejects forged checkpoints and keeps the original rollback point
   - Expected: nested.cursor_bytes equals `0u64`
   - Expected: arena.rollback(forged) is false
   - Expected: arena.cursor_bytes equals `8u64`
   - Expected: arena.rollback(original) is true
   - Expected: arena.cursor_bytes equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects forged checkpoints and keeps the original rollback point")
val arena = DomainArenaV1.from_sealed_profile(15u64, relaxed_test_profile_v1(64u64))
val original = arena.checkpoint()
arena.try_allocate(8u64, ARENA_CONTEXT_NORMAL)
val nested = arena.checkpoint()
expect(nested.cursor_bytes).to_equal(0u64)
val forged = ArenaCheckpointV1(
    arena_id: 15u64, domain_id: 4u32, generation: 1u64,
    cursor_bytes: 32u64, allocation_count: 1u32, publication_epoch: 0u64
)
expect(arena.rollback(forged)).to_equal(false)
expect(arena.cursor_bytes).to_equal(8u64)
expect(arena.rollback(original)).to_equal(true)
expect(arena.cursor_bytes).to_equal(0u64)
```

</details>

#### rejects malformed relaxed profiles before cursor mutation

- rejects malformed relaxed profiles before cursor mutation
   - Expected: receipt.reason equals `ARENA_EXHAUSTION_INVALID_REQUEST`
   - Expected: false is true
   - Expected: arena.cursor_bytes equals `0u64`
   - Expected: receipt.reason equals `ARENA_EXHAUSTION_INVALID_REQUEST`
   - Expected: false is true
   - Expected: receipt.reason equals `ARENA_EXHAUSTION_FORBIDDEN_CONTEXT`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects malformed relaxed profiles before cursor mutation")
var invalid = relaxed_test_profile_v1(64u64)
invalid.strict_default = false
val arena = DomainArenaV1.from_sealed_profile(16u64, invalid)
arena.checkpoint()
match arena.try_allocate(8u64, ARENA_CONTEXT_NORMAL):
    DomainArenaAllocationV1.Exhausted(receipt):
        expect(receipt.reason).to_equal(ARENA_EXHAUSTION_INVALID_REQUEST)
    DomainArenaAllocationV1.Allocated(reference):
        expect(false).to_equal(true)
expect(arena.cursor_bytes).to_equal(0u64)

var bad_alignment = relaxed_test_profile_v1(64u64)
bad_alignment.alignment = 3u32
val alignment_arena = DomainArenaV1.from_sealed_profile(18u64, bad_alignment)
alignment_arena.checkpoint()
match alignment_arena.try_allocate(8u64, ARENA_CONTEXT_NORMAL):
    DomainArenaAllocationV1.Exhausted(receipt):
        expect(receipt.reason).to_equal(ARENA_EXHAUSTION_INVALID_REQUEST)
    DomainArenaAllocationV1.Allocated(reference):
        expect(false).to_equal(true)

val unknown_context_arena = DomainArenaV1.from_sealed_profile(19u64, relaxed_test_profile_v1(64u64))
unknown_context_arena.checkpoint()
match unknown_context_arena.try_allocate(8u64, 65u64):
    DomainArenaAllocationV1.Exhausted(receipt):
        expect(receipt.reason).to_equal(ARENA_EXHAUSTION_FORBIDDEN_CONTEXT)
    DomainArenaAllocationV1.Allocated(reference):
        expect(false).to_equal(true)
```

</details>

#### rejects profile mutation after sealing and forged zero-size references

- rejects profile mutation after sealing and forged zero-size references
   - Expected: receipt.reason equals `ARENA_EXHAUSTION_INVALID_REQUEST`
   - Expected: false is true
   - Expected: arena.commit(checkpoint) is false
   - Expected: arena.rollback(checkpoint) is true
   - Expected: arena.validates(forged) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects profile mutation after sealing and forged zero-size references")
val arena = DomainArenaV1.from_sealed_profile(20u64, relaxed_test_profile_v1(64u64))
val checkpoint = arena.checkpoint()
arena.profile.quota_bytes = 128u64
match arena.try_allocate(8u64, ARENA_CONTEXT_NORMAL):
    DomainArenaAllocationV1.Exhausted(receipt):
        expect(receipt.reason).to_equal(ARENA_EXHAUSTION_INVALID_REQUEST)
    DomainArenaAllocationV1.Allocated(reference):
        expect(false).to_equal(true)
expect(arena.commit(checkpoint)).to_equal(false)
expect(arena.rollback(checkpoint)).to_equal(true)

val forged = DomainArenaRefV1(
    arena_id: 20u64, domain_id: 4u32, generation: arena.committed_generation,
    offset_bytes: arena.committed_cursor_bytes, size_bytes: 0u64
)
expect(arena.validates(forged)).to_equal(false)
```

</details>

#### injects every registered arena failure boundary without cross-domain mutation

- injects every registered arena failure boundary without cross-domain mutation
   - Expected: false is true
   - Expected: protected_arena.commit(protected_checkpoint) is true
   - Expected: fault_arena.commit(baseline_checkpoint) is true
   - Expected: domain_arena_committed_state_hash_v1(fault_arena) == isolated_before_hash is false
   - Expected: fault_arena.committed_state.generation equals `fault_arena.committed_generation`
   - Expected: fault_arena.committed_state.publication_epoch equals `fault_arena.publication_epoch`
   - Expected: fault_arena.arm_fault_once(ARENA_FAULT_BEFORE_CURSOR_ADVANCE) is true
   - Expected: receipt.reason equals `ARENA_EXHAUSTION_INJECTED_FAULT`
   - Expected: false is true
   - Expected: fault_arena.cursor_bytes equals `0u64`
   - Expected: fault_arena.rollback(allocation_checkpoint) is true
   - Expected: arena_failure_injection_ledger_entry_valid_v1(allocation_ledger) is true
   - Expected: fault_arena.arm_fault_once(ARENA_FAULT_BEFORE_PUBLICATION) is true
   - Expected: fault_arena.commit(publication_checkpoint) is false
   - Expected: fault_arena.publication_epoch equals `1u64`
   - Expected: fault_arena.rollback(publication_checkpoint) is true
   - Expected: fault_arena.committed_generation equals `1u64`
   - Expected: fault_arena.injected_fault_count equals `2u64`
   - Expected: arena_failure_injection_ledger_entry_valid_v1(publication_ledger) is true
   - Expected: arena_sha256_lower_hex_valid_v1("A77be0b0e329204db951474c0085526c103049d51ce6ae6a194e5f9312bd11b3") is false
   - Expected: protected_arena.publication_epoch equals `1u64`
   - Expected: protected_arena.validates(protected_ref) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 125 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("injects every registered arena failure boundary without cross-domain mutation")
val protected_arena = DomainArenaV1.from_sealed_profile(
    21u64, relaxed_test_profile_v1(64u64)
)
val protected_checkpoint = protected_arena.checkpoint()
var protected_ref = DomainArenaRefV1(
    arena_id: 0u64, domain_id: 0u32, generation: 0u64,
    offset_bytes: 0u64, size_bytes: 0u64
)
match protected_arena.try_allocate(16u64, ARENA_CONTEXT_NORMAL):
    DomainArenaAllocationV1.Allocated(reference):
        protected_ref = reference
    DomainArenaAllocationV1.Exhausted(receipt):
        expect(false).to_equal(true)
expect(protected_arena.commit(protected_checkpoint)).to_equal(true)
val isolated_before_hash = domain_arena_committed_state_hash_v1(protected_arena)

val fault_arena = DomainArenaV1.from_sealed_profile(
    22u64, relaxed_test_profile_v1(64u64)
)
val baseline_checkpoint = fault_arena.checkpoint()
fault_arena.try_allocate(8u64, ARENA_CONTEXT_NORMAL)
expect(fault_arena.commit(baseline_checkpoint)).to_equal(true)
expect(domain_arena_committed_state_hash_v1(fault_arena)).to_equal(
    "632e0465fb204ef8d4cb278ccb58190f1adfda98ac086ad743af1247a5dfefdd"
)
expect(domain_arena_committed_state_hash_v1(fault_arena) == isolated_before_hash).to_equal(false)
expect(fault_arena.committed_state.generation).to_equal(fault_arena.committed_generation)
expect(fault_arena.committed_state.publication_epoch).to_equal(fault_arena.publication_epoch)
val allocation_checkpoint = fault_arena.checkpoint()
val allocation_before_hash = domain_arena_committed_state_hash_v1(fault_arena)
expect(fault_arena.arm_fault_once(ARENA_FAULT_BEFORE_CURSOR_ADVANCE)).to_equal(true)
match fault_arena.try_allocate(8u64, ARENA_CONTEXT_NORMAL):
    DomainArenaAllocationV1.Exhausted(receipt):
        expect(receipt.reason).to_equal(ARENA_EXHAUSTION_INJECTED_FAULT)
    DomainArenaAllocationV1.Allocated(reference):
        expect(false).to_equal(true)
expect(fault_arena.cursor_bytes).to_equal(0u64)
expect(fault_arena.rollback(allocation_checkpoint)).to_equal(true)
val allocation_after_hash = domain_arena_committed_state_hash_v1(fault_arena)
var allocation_ledger = ArenaFailureInjectionLedgerEntryV1(
    schema_version: 1u16, run_id: "arena-ledger-run-1",
    fault_point: ARENA_FAULT_BEFORE_CURSOR_ADVANCE,
    fault_name: arena_failure_point_name_v1(ARENA_FAULT_BEFORE_CURSOR_ADVANCE),
    occurrence: 1u16, subject_arena_id: 22u64, subject_generation: 1u64,
    isolated_arena_id: 21u64, isolated_generation: 1u64,
    subject_before_hash: allocation_before_hash,
    subject_after_hash: allocation_after_hash,
    isolated_before_hash: isolated_before_hash,
    isolated_after_hash: domain_arena_committed_state_hash_v1(protected_arena),
    injected: true, rolled_back: true, row_hash: ""
)
allocation_ledger.row_hash = arena_failure_injection_ledger_row_hash_v1(allocation_ledger)
expect(arena_failure_injection_ledger_entry_valid_v1(allocation_ledger)).to_equal(true)

val publication_checkpoint = fault_arena.checkpoint()
val publication_before_hash = domain_arena_committed_state_hash_v1(fault_arena)
fault_arena.try_allocate(8u64, ARENA_CONTEXT_NORMAL)
expect(fault_arena.arm_fault_once(ARENA_FAULT_BEFORE_PUBLICATION)).to_equal(true)
expect(fault_arena.commit(publication_checkpoint)).to_equal(false)
expect(fault_arena.publication_epoch).to_equal(1u64)
expect(fault_arena.rollback(publication_checkpoint)).to_equal(true)
expect(fault_arena.committed_generation).to_equal(1u64)
expect(fault_arena.injected_fault_count).to_equal(2u64)
var publication_ledger = ArenaFailureInjectionLedgerEntryV1(
    schema_version: 1u16, run_id: "arena-ledger-run-1",
    fault_point: ARENA_FAULT_BEFORE_PUBLICATION,
    fault_name: arena_failure_point_name_v1(ARENA_FAULT_BEFORE_PUBLICATION),
    occurrence: 1u16, subject_arena_id: 22u64, subject_generation: 1u64,
    isolated_arena_id: 21u64, isolated_generation: 1u64,
    subject_before_hash: publication_before_hash,
    subject_after_hash: domain_arena_committed_state_hash_v1(fault_arena),
    isolated_before_hash: isolated_before_hash,
    isolated_after_hash: domain_arena_committed_state_hash_v1(protected_arena),
    injected: true, rolled_back: true, row_hash: ""
)
publication_ledger.row_hash = arena_failure_injection_ledger_row_hash_v1(publication_ledger)
expect(arena_failure_injection_ledger_entry_valid_v1(publication_ledger)).to_equal(true)
val complete_ledger = [allocation_ledger, publication_ledger]
expect(arena_failure_injection_ledger_complete_v1(
    complete_ledger, "arena-ledger-run-1", 22u64, 1u64,
    allocation_before_hash, 21u64, 1u64, isolated_before_hash
)).to_equal(true)
expect(arena_failure_injection_ledger_complete_v1(
    [allocation_ledger, allocation_ledger], "arena-ledger-run-1",
    22u64, 1u64, allocation_before_hash, 21u64, 1u64, isolated_before_hash
)).to_equal(false)
expect(arena_failure_injection_ledger_complete_v1(
    [allocation_ledger], "arena-ledger-run-1", 22u64, 1u64,
    allocation_before_hash, 21u64, 1u64, isolated_before_hash
)).to_equal(false)
expect(arena_failure_injection_ledger_complete_v1(
    complete_ledger, "replayed-run", 22u64, 1u64,
    allocation_before_hash, 21u64, 1u64, isolated_before_hash
)).to_equal(false)
expect(arena_failure_injection_ledger_complete_v1(
    complete_ledger, "arena-ledger-run-1", 21u64, 1u64,
    isolated_before_hash, 22u64, 1u64, allocation_before_hash
)).to_equal(false)
var relabeled = publication_ledger
relabeled.run_id = "replayed-run"
relabeled.row_hash = arena_failure_injection_ledger_row_hash_v1(relabeled)
expect(arena_failure_injection_ledger_complete_v1(
    [allocation_ledger, relabeled], "arena-ledger-run-1", 22u64, 1u64,
    allocation_before_hash, 21u64, 1u64, isolated_before_hash
)).to_equal(false)
expect(arena_sha256_lower_hex_valid_v1("A77be0b0e329204db951474c0085526c103049d51ce6ae6a194e5f9312bd11b3")).to_equal(false)

expect(protected_arena.publication_epoch).to_equal(1u64)
expect(protected_arena.validates(protected_ref)).to_equal(true)
for scenario_id in [
    "MCI-ARENA-001", "MCI-ARENA-002", "MCI-ARENA-003", "MCI-ARENA-004",
    "MCI-ARENA-005", "MCI-ARENA-006", "MCI-ARENA-007", "MCI-ARENA-008",
    "MCI-ARENA-009", "MCI-ARENA-010", "MCI-ARENA-011", "MCI-ARENA-012"
]:
    print(domain_arena_evidence_scenario_row_v1(scenario_id))
print(domain_arena_evidence_profile_row_v1(
    relaxed_allocation_profile_hash_v1(relaxed_test_profile_v1(64u64))
))
print(domain_arena_evidence_snapshot_row_v1(
    domain_arena_committed_state_hash_v1(fault_arena)
))
print(domain_arena_evidence_ledger_row_v1(allocation_ledger))
print(domain_arena_evidence_ledger_row_v1(publication_ledger))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/mission_critical/domain_arena_v1_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering sealed relaxed-allocation domain arena v1.
- sealed relaxed-allocation domain arena v1

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bead3eab5e763ec8d77451d120d0b283ae7ecc738db8ce6c3b4e3969ccd22a9d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bead3eab5e763ec8d77451d120d0b283ae7ecc738db8ce6c3b4e3969ccd22a9d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bead3eab5e763ec8d77451d120d0b283ae7ecc738db8ce6c3b4e3969ccd22a9d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/nogc_sync_mut/mission_critical/domain_arena_v1_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/mission_critical/domain_arena_v1_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/mission_critical/domain_arena_v1_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/mission_critical/domain_arena_v1_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/mission_critical/domain_arena_v1_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_sync_mut/mission_critical/domain_arena_v1_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses a canonical SHA-256 identity for the sealed profile' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/mission_critical/domain_arena_v1_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'enumerates the complete named failure-point registry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/mission_critical/domain_arena_v1_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds every profile and committed-snapshot field into its hash' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
