# Execution Profile Contract Specification

> Tests covering device mask bit vocabulary, execution mode bit vocabulary, StageFallbackPolicy vocabulary, StorageCapabilityTier vocabulary, wire booleans, StageExecutionProfile encodes to the hand-derived golden bytes, StageCapabilities encodes to the hand-derived golden bytes, record magics are distinct, StageExecutionProfile round-trips, StageCapabilities round-trips, decode rejects malformed profile buffers, decode rejects malformed capabilities buffers, encode enforces the same invariants as decode, three modes everywhere, and no silent fallback, capabilities decide satisfaction before a stage ever runs, contract version is pinned.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 81 | 81 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Execution Profile Contract Specification

## Scenarios

### device mask bit vocabulary

#### assigns one bit per cost channel section 21.2 budgets separately

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- assigns one bit per cost channel section 21.2 budgets separately


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assigns one bit per cost channel section 21.2 budgets separately")
assert_equal(DEVICE_BIT_CPU_SCALAR, 1)
assert_equal(DEVICE_BIT_CPU_SIMD, 2)
assert_equal(DEVICE_BIT_GPU, 4)
assert_equal(DEVICE_BIT_STORAGE, 8)
```

</details>

#### declares exactly four bits and no fifth

- declares exactly four bits and no fifth


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declares exactly four bits and no fifth")
assert_equal(DEVICE_MASK_BIT_COUNT, 4)
assert_equal(DEVICE_MASK_KNOWN, 15)
```

</details>

#### rejects a set reserved bit rather than ignoring it

- rejects a set reserved bit rather than ignoring it


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a set reserved bit rather than ignoring it")
assert_true(device_mask_valid(DEVICE_MASK_KNOWN))
assert_false(device_mask_valid(16))
assert_false(device_mask_valid(DEVICE_MASK_KNOWN | 16))
```

</details>

#### rejects a mask that permits no executor at all

- rejects a mask that permits no executor at all


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a mask that permits no executor at all")
assert_false(device_mask_valid(0))
assert_false(device_mask_valid(-1))
```

</details>

#### reports containment for each individual bit

- reports containment for each individual bit


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports containment for each individual bit")
assert_true(device_mask_has(DEVICE_MASK_KNOWN, DEVICE_BIT_GPU))
assert_false(device_mask_has(DEVICE_BIT_CPU_SCALAR, DEVICE_BIT_GPU))
```

</details>

#### covers a subset but never a superset

- covers a subset but never a superset


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers a subset but never a superset")
assert_true(device_mask_covers(DEVICE_MASK_KNOWN, DEVICE_BIT_GPU))
assert_true(device_mask_covers(DEVICE_MASK_KNOWN, DEVICE_MASK_KNOWN))
assert_false(device_mask_covers(DEVICE_BIT_CPU_SCALAR, DEVICE_BIT_GPU))
```

</details>

#### renders bits in declaration order so the spelling is a function of the bits

- renders bits in declaration order so the spelling is a function of the bits


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders bits in declaration order so the spelling is a function of the bits")
assert_equal(device_mask_to_text(DEVICE_BIT_CPU_SCALAR), "cpu_scalar")
assert_equal(device_mask_to_text(DEVICE_BIT_GPU), "gpu")
assert_equal(device_mask_to_text(DEVICE_MASK_KNOWN),
             "cpu_scalar|cpu_simd|gpu|storage")
```

</details>

#### bridges to and from the already-existing DeviceMask type

- bridges to and from the already-existing DeviceMask type


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bridges to and from the already-existing DeviceMask type")
assert_equal(device_mask_bits(device_mask_of(DEVICE_MASK_KNOWN)),
             DEVICE_MASK_KNOWN)
assert_equal(device_mask_bits(DeviceMask(bits: 5)), 5)
```

</details>

### execution mode bit vocabulary

#### derives each bit from the already-frozen ExecutionMode discriminant

- derives each bit from the already-frozen ExecutionMode discriminant


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("derives each bit from the already-frozen ExecutionMode discriminant")
assert_equal(mode_bit(ExecutionMode.CpuReference), MODE_BIT_CPU_REFERENCE)
assert_equal(mode_bit(ExecutionMode.HybridVectorGpu),
             MODE_BIT_HYBRID_VECTOR_GPU)
assert_equal(mode_bit(ExecutionMode.ResidentGpu), MODE_BIT_RESIDENT_GPU)
```

</details>

#### keeps the mask exactly three bits wide

- keeps the mask exactly three bits wide


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the mask exactly three bits wide")
assert_equal(MODE_MASK_KNOWN, 7)
assert_equal(MODE_BIT_CPU_REFERENCE | MODE_BIT_HYBRID_VECTOR_GPU
                 | MODE_BIT_RESIDENT_GPU, MODE_MASK_KNOWN)
```

</details>

#### rejects an empty or reserved-bit mode mask

- rejects an empty or reserved-bit mode mask


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an empty or reserved-bit mode mask")
assert_true(mode_mask_valid(MODE_MASK_KNOWN))
assert_false(mode_mask_valid(0))
assert_false(mode_mask_valid(8))
```

</details>

<details>
<summary>Advanced: classifies exactly the two device columns of the mode matrix as GPU</summary>

#### classifies exactly the two device columns of the mode matrix as GPU

- classifies exactly the two device columns of the mode matrix as GPU


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies exactly the two device columns of the mode matrix as GPU")
assert_false(mode_mask_uses_gpu(MODE_BIT_CPU_REFERENCE))
assert_true(mode_mask_uses_gpu(MODE_BIT_HYBRID_VECTOR_GPU))
assert_true(mode_mask_uses_gpu(MODE_BIT_RESIDENT_GPU))
```

</details>


</details>

#### answers membership per mode

- answers membership per mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("answers membership per mode")
assert_true(mode_mask_has(MODE_MASK_KNOWN, ExecutionMode.ResidentGpu))
assert_false(mode_mask_has(MODE_BIT_CPU_REFERENCE,
                           ExecutionMode.ResidentGpu))
```

</details>

### StageFallbackPolicy vocabulary

#### carries the three stopping points of the resident-hybrid-cpu ladder

- carries the three stopping points of the resident-hybrid-cpu ladder


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("carries the three stopping points of the resident-hybrid-cpu ladder")
assert_equal(STAGE_FALLBACK_POLICY_COUNT, 3)
assert_equal(STAGE_FALLBACK_POLICY_MAX, 2)
assert_equal(stage_fallback_policy_to_u8(StageFallbackPolicy.Forbid), 0)
assert_equal(stage_fallback_policy_to_u8(StageFallbackPolicy.AllowHybrid), 1)
assert_equal(stage_fallback_policy_to_u8(StageFallbackPolicy.AllowCpu), 2)
```

</details>

#### round-trips every discriminant through from_u8

- round-trips every discriminant through from_u8


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips every discriminant through from_u8")
var i = 0
var mismatches = 0
while i <= STAGE_FALLBACK_POLICY_MAX:
    if stage_fallback_policy_to_u8(stage_fallback_policy_from_u8(i)) != i:
        mismatches = mismatches + 1
    i = i + 1
assert_equal(mismatches, 0)
```

</details>

#### rejects a discriminant past the end of the frozen enum

- rejects a discriminant past the end of the frozen enum


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a discriminant past the end of the frozen enum")
assert_true(stage_fallback_policy_valid(2))
assert_false(stage_fallback_policy_valid(3))
assert_false(stage_fallback_policy_valid(-1))
assert_false(stage_fallback_policy_valid(255))
```

</details>

#### pins an unknown discriminant to the SAFE rung, never a permissive one

- pins an unknown discriminant to the SAFE rung, never a permissive one


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pins an unknown discriminant to the SAFE rung, never a permissive one")
assert_equal(stage_fallback_policy_to_u8(stage_fallback_policy_from_u8(99)),
             0)
```

</details>

#### spells each policy stably

- spells each policy stably


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("spells each policy stably")
assert_equal(stage_fallback_policy_to_text(StageFallbackPolicy.Forbid),
             "forbid")
assert_equal(stage_fallback_policy_to_text(StageFallbackPolicy.AllowHybrid),
             "allow_hybrid")
assert_equal(stage_fallback_policy_to_text(StageFallbackPolicy.AllowCpu),
             "allow_cpu")
```

</details>

#### reports CPU permission for AllowCpu alone

- reports CPU permission for AllowCpu alone


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports CPU permission for AllowCpu alone")
assert_false(stage_fallback_policy_permits_cpu(StageFallbackPolicy.Forbid))
assert_false(stage_fallback_policy_permits_cpu(StageFallbackPolicy.AllowHybrid))
assert_true(stage_fallback_policy_permits_cpu(StageFallbackPolicy.AllowCpu))
```

</details>

### StorageCapabilityTier vocabulary

#### carries section 20.7's three tiers in the order printed there

- carries section 20.7's three tiers in the order printed there


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("carries section 20.7's three tiers in the order printed there")
assert_equal(STORAGE_TIER_COUNT, 3)
assert_equal(STORAGE_TIER_MAX, 2)
assert_equal(storage_tier_to_u8(StorageCapabilityTier.Staged), 0)
assert_equal(storage_tier_to_u8(StorageCapabilityTier.Direct), 1)
assert_equal(storage_tier_to_u8(StorageCapabilityTier.DeviceInitiated), 2)
```

</details>

#### round-trips every discriminant and rejects the one past the end

- round-trips every discriminant and rejects the one past the end


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips every discriminant and rejects the one past the end")
var i = 0
var mismatches = 0
while i <= STORAGE_TIER_MAX:
    if storage_tier_to_u8(storage_tier_from_u8(i)) != i:
        mismatches = mismatches + 1
    i = i + 1
assert_equal(mismatches, 0)
assert_false(storage_tier_valid(3))
assert_false(storage_tier_valid(-1))
```

</details>

#### spells each tier the way section 20.7 spells it

- spells each tier the way section 20.7 spells it


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("spells each tier the way section 20.7 spells it")
assert_equal(storage_tier_to_text(StorageCapabilityTier.Staged), "staged")
assert_equal(storage_tier_to_text(StorageCapabilityTier.Direct), "direct")
assert_equal(storage_tier_to_text(StorageCapabilityTier.DeviceInitiated),
             "device_initiated")
```

</details>

#### derives each mask bit from the tier discriminant

- derives each mask bit from the tier discriminant


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("derives each mask bit from the tier discriminant")
assert_equal(storage_tier_bit(StorageCapabilityTier.Staged),
             STORAGE_BIT_STAGED)
assert_equal(storage_tier_bit(StorageCapabilityTier.Direct),
             STORAGE_BIT_DIRECT)
assert_equal(storage_tier_bit(StorageCapabilityTier.DeviceInitiated),
             STORAGE_BIT_DEVICE_INITIATED)
assert_equal(STORAGE_MASK_KNOWN, 7)
```

</details>

#### requires the mandatory staged path whenever any tier is claimed

- requires the mandatory staged path whenever any tier is claimed


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires the mandatory staged path whenever any tier is claimed")
assert_true(storage_mask_valid(0))
assert_true(storage_mask_valid(STORAGE_BIT_STAGED))
assert_true(storage_mask_valid(STORAGE_BIT_STAGED | STORAGE_BIT_DIRECT))
assert_false(storage_mask_valid(STORAGE_BIT_DIRECT))
assert_false(storage_mask_valid(STORAGE_BIT_DEVICE_INITIATED))
```

</details>

#### rejects a set reserved storage bit

- rejects a set reserved storage bit


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a set reserved storage bit")
assert_false(storage_mask_valid(STORAGE_BIT_STAGED | 8))
```

</details>

#### answers tier membership

- answers tier membership


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("answers tier membership")
assert_true(storage_mask_has(STORAGE_MASK_KNOWN,
                             StorageCapabilityTier.DeviceInitiated))
assert_false(storage_mask_has(STORAGE_BIT_STAGED,
                              StorageCapabilityTier.Direct))
```

</details>

### wire booleans

#### encodes as exactly zero or one

- encodes as exactly zero or one


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes as exactly zero or one")
assert_equal(wire_bool_to_u8(true), 1)
assert_equal(wire_bool_to_u8(false), 0)
```

</details>

#### refuses to coerce any other byte to true

- refuses to coerce any other byte to true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses to coerce any other byte to true")
assert_true(wire_bool_valid(0))
assert_true(wire_bool_valid(1))
assert_false(wire_bool_valid(2))
assert_false(wire_bool_valid(255))
assert_false(wire_bool_valid(-1))
```

</details>

#### round-trips both values

- round-trips both values


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips both values")
assert_true(wire_bool_from_u8(wire_bool_to_u8(true)))
assert_false(wire_bool_from_u8(wire_bool_to_u8(false)))
```

</details>

### StageExecutionProfile encodes to the hand-derived golden bytes

#### matches the cpu_reference vector byte for byte

- matches the cpu_reference vector byte for byte


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches the cpu_reference vector byte for byte")
assert_equal(wire_to_hex(encode_stage_execution_profile(
                 stage_execution_profile_cpu_reference())),
             GOLDEN_PROFILE_CPU_REFERENCE)
```

</details>

#### matches the resident/allow_cpu vector byte for byte

- matches the resident/allow_cpu vector byte for byte


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches the resident/allow_cpu vector byte for byte")
assert_equal(wire_to_hex(encode_stage_execution_profile(
                 fixture_resident_allow_cpu())),
             GOLDEN_PROFILE_RESIDENT_ALLOW_CPU)
```

</details>

#### matches the resident/allow_hybrid vector byte for byte

- matches the resident/allow_hybrid vector byte for byte


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches the resident/allow_hybrid vector byte for byte")
assert_equal(wire_to_hex(encode_stage_execution_profile(
                 fixture_resident_allow_hybrid())),
             GOLDEN_PROFILE_RESIDENT_ALLOW_HYBRID)
```

</details>

#### occupies exactly the frozen extent

- occupies exactly the frozen extent


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("occupies exactly the frozen extent")
assert_equal(STAGE_EXECUTION_PROFILE_LEN, 48)
assert_equal(encode_stage_execution_profile(
                 stage_execution_profile_cpu_reference()).len(), 56)
```

</details>

### StageCapabilities encodes to the hand-derived golden bytes

#### matches the gpu backend vector byte for byte

- matches the gpu backend vector byte for byte


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches the gpu backend vector byte for byte")
assert_equal(wire_to_hex(encode_stage_capabilities(fixture_caps_gpu())),
             GOLDEN_CAPABILITIES_GPU)
```

</details>

#### matches the cpu backend vector byte for byte

- matches the cpu backend vector byte for byte


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches the cpu backend vector byte for byte")
assert_equal(wire_to_hex(encode_stage_capabilities(fixture_caps_cpu())),
             GOLDEN_CAPABILITIES_CPU)
```

</details>

#### occupies exactly its head plus its one text field

- occupies exactly its head plus its one text field


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("occupies exactly its head plus its one text field")
assert_equal(STAGE_CAPABILITIES_HEAD_LEN, 16)
assert_equal(encode_stage_capabilities(fixture_caps_gpu()).len(), 31)
```

</details>

### record magics are distinct

#### gives the two records different magics so a cross-typed buffer fails

- gives the two records different magics so a cross-typed buffer fails


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gives the two records different magics so a cross-typed buffer fails")
assert_true(profile_magic_execution() != profile_magic_capabilities())
```

</details>

### StageExecutionProfile round-trips

#### reconstructs the cpu_reference profile

- reconstructs the cpu_reference profile


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reconstructs the cpu_reference profile")
val p = stage_execution_profile_cpu_reference()
val r = decode_stage_execution_profile(encode_stage_execution_profile(p))
assert_true(r.ok)
assert_true(stage_execution_profile_equal(r.value, p))
```

</details>

#### reconstructs every numeric slot of the resident profile

- reconstructs every numeric slot of the resident profile


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reconstructs every numeric slot of the resident profile")
val p = fixture_resident_allow_cpu()
val r = decode_stage_execution_profile(encode_stage_execution_profile(p))
assert_true(r.ok)
assert_true(stage_execution_profile_equal(r.value, p))
assert_equal(r.value.host_memory_budget, 1073741824)
assert_equal(r.value.device_memory_budget, 2147483648)
assert_equal(r.value.latency_target_us, 5000)
assert_equal(r.value.throughput_target, 1000000)
assert_equal(r.value.allowed_devices, DEVICE_MASK_KNOWN)
assert_equal(execution_mode_to_u8(r.value.mode), 2)
assert_equal(stage_fallback_policy_to_u8(r.value.fallback), 2)
assert_equal(verification_policy_to_u8(r.value.verification), 4)
assert_false(r.value.deterministic)
```

</details>

#### reconstructs the allow_hybrid profile

- reconstructs the allow_hybrid profile


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reconstructs the allow_hybrid profile")
val p = fixture_resident_allow_hybrid()
val r = decode_stage_execution_profile(encode_stage_execution_profile(p))
assert_true(r.ok)
assert_true(stage_execution_profile_equal(r.value, p))
```

</details>

### StageCapabilities round-trips

#### reconstructs the gpu backend record including its name

- reconstructs the gpu backend record including its name


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reconstructs the gpu backend record including its name")
val c = fixture_caps_gpu()
val r = decode_stage_capabilities(encode_stage_capabilities(c))
assert_true(r.ok)
assert_true(stage_capabilities_equal(r.value, c))
assert_equal(r.value.backend, "gpu")
assert_equal(r.value.supported_modes, MODE_MASK_KNOWN)
assert_equal(r.value.device_mask, DEVICE_MASK_KNOWN)
```

</details>

#### reconstructs the cpu backend record

- reconstructs the cpu backend record


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reconstructs the cpu backend record")
val c = fixture_caps_cpu()
val r = decode_stage_capabilities(encode_stage_capabilities(c))
assert_true(r.ok)
assert_true(stage_capabilities_equal(r.value, c))
assert_equal(r.value.backend, "cpu")
assert_equal(r.value.storage_tiers, 0)
```

</details>

### decode rejects malformed profile buffers

#### rejects an empty buffer

- rejects an empty buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an empty buffer")
val empty: [u8] = []
assert_false(decode_stage_execution_profile(empty).ok)
```

</details>

#### rejects a truncated buffer

- rejects a truncated buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a truncated buffer")
val b = encode_stage_execution_profile(fixture_resident_allow_cpu())
assert_false(decode_stage_execution_profile(truncated(b, 40)).ok)
assert_false(decode_stage_execution_profile(truncated(b, 55)).ok)
```

</details>

#### rejects trailing bytes rather than tolerating them

- rejects trailing bytes rather than tolerating them


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects trailing bytes rather than tolerating them")
val b = encode_stage_execution_profile(fixture_resident_allow_cpu())
assert_false(decode_stage_execution_profile(extended(b)).ok)
```

</details>

#### rejects a capabilities buffer handed to the profile decoder

- rejects a capabilities buffer handed to the profile decoder


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a capabilities buffer handed to the profile decoder")
assert_false(decode_stage_execution_profile(
    encode_stage_capabilities(fixture_caps_gpu())).ok)
```

</details>

#### rejects a non-zero envelope reserved field

- rejects a non-zero envelope reserved field


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a non-zero envelope reserved field")
val b = encode_stage_execution_profile(fixture_resident_allow_cpu())
assert_false(decode_stage_execution_profile(corrupt_byte(b, 6, 1)).ok)
```

</details>

#### rejects an unknown envelope version

- rejects an unknown envelope version


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an unknown envelope version")
val b = encode_stage_execution_profile(fixture_resident_allow_cpu())
assert_false(decode_stage_execution_profile(corrupt_byte(b, 4, 2)).ok)
```

</details>

#### rejects an unknown mode discriminant instead of defaulting

- rejects an unknown mode discriminant instead of defaulting


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an unknown mode discriminant instead of defaulting")
val b = encode_stage_execution_profile(fixture_resident_allow_cpu())
assert_false(decode_stage_execution_profile(corrupt_byte(b, 12, 3)).ok)
```

</details>

#### rejects a deterministic byte that is neither zero nor one

- rejects a deterministic byte that is neither zero nor one


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a deterministic byte that is neither zero nor one")
val b = encode_stage_execution_profile(fixture_resident_allow_cpu())
assert_false(decode_stage_execution_profile(corrupt_byte(b, 13, 2)).ok)
```

</details>

#### rejects an unknown fallback policy discriminant

- rejects an unknown fallback policy discriminant


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an unknown fallback policy discriminant")
val b = encode_stage_execution_profile(fixture_resident_allow_cpu())
assert_false(decode_stage_execution_profile(corrupt_byte(b, 14, 3)).ok)
```

</details>

#### rejects an unknown verification policy discriminant

- rejects an unknown verification policy discriminant


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an unknown verification policy discriminant")
val b = encode_stage_execution_profile(fixture_resident_allow_cpu())
assert_false(decode_stage_execution_profile(corrupt_byte(b, 15, 5)).ok)
```

</details>

#### rejects a set reserved device bit arriving on the wire

- rejects a set reserved device bit arriving on the wire


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a set reserved device bit arriving on the wire")
val b = encode_stage_execution_profile(fixture_resident_allow_cpu())
assert_false(decode_stage_execution_profile(corrupt_byte(b, 48, 31)).ok)
```

</details>

#### rejects a decoded profile whose mode its own device mask forbids

- rejects a decoded profile whose mode its own device mask forbids


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a decoded profile whose mode its own device mask forbids")
# allowed_devices drops the GPU bit while mode stays resident_gpu.
val b = encode_stage_execution_profile(fixture_resident_allow_cpu())
assert_false(decode_stage_execution_profile(corrupt_byte(b, 48, 3)).ok)
```

</details>

### decode rejects malformed capabilities buffers

#### rejects an empty and a truncated buffer

- rejects an empty and a truncated buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an empty and a truncated buffer")
val empty: [u8] = []
assert_false(decode_stage_capabilities(empty).ok)
val b = encode_stage_capabilities(fixture_caps_gpu())
assert_false(decode_stage_capabilities(truncated(b, 20)).ok)
```

</details>

#### rejects trailing bytes

- rejects trailing bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects trailing bytes")
val b = encode_stage_capabilities(fixture_caps_gpu())
assert_false(decode_stage_capabilities(extended(b)).ok)
```

</details>

#### rejects a profile buffer handed to the capabilities decoder

- rejects a profile buffer handed to the capabilities decoder


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a profile buffer handed to the capabilities decoder")
assert_false(decode_stage_capabilities(
    encode_stage_execution_profile(fixture_resident_allow_cpu())).ok)
```

</details>

#### rejects a reserved mode-mask bit

- rejects a reserved mode-mask bit


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a reserved mode-mask bit")
val b = encode_stage_capabilities(fixture_caps_gpu())
assert_false(decode_stage_capabilities(corrupt_byte(b, 12, 15)).ok)
```

</details>

#### rejects a storage mask claiming direct without the mandatory staged

- rejects a storage mask claiming direct without the mandatory staged


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a storage mask claiming direct without the mandatory staged")
val b = encode_stage_capabilities(fixture_caps_gpu())
assert_false(decode_stage_capabilities(corrupt_byte(b, 13, 2)).ok)
```

</details>

#### rejects a GPU-mode claim without the gpu device bit

- rejects a GPU-mode claim without the gpu device bit


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a GPU-mode claim without the gpu device bit")
val b = encode_stage_capabilities(fixture_caps_gpu())
assert_false(decode_stage_capabilities(corrupt_byte(b, 16, 3)).ok)
```

</details>

### encode enforces the same invariants as decode

#### refuses a resident profile whose device mask forbids the GPU

- refuses a resident profile whose device mask forbids the GPU


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a resident profile whose device mask forbids the GPU")
val p = stage_execution_profile(ExecutionMode.ResidentGpu, true,
                                0, 0, 0, 0,
                                StageFallbackPolicy.Forbid,
                                VerificationPolicy.Off,
                                DEVICE_BIT_CPU_SCALAR)
assert_false(stage_execution_profile_valid(p))
assert_false(stage_execution_profile_encodable(p))
assert_equal(encode_stage_execution_profile(p).len(), 0)
```

</details>

#### refuses AllowCpu when the scalar CPU is not permitted

- refuses AllowCpu when the scalar CPU is not permitted


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses AllowCpu when the scalar CPU is not permitted")
val p = stage_execution_profile(ExecutionMode.ResidentGpu, true,
                                0, 0, 0, 0,
                                StageFallbackPolicy.AllowCpu,
                                VerificationPolicy.Off,
                                DEVICE_BIT_GPU)
assert_false(profile_fallback_reachable(p))
assert_equal(encode_stage_execution_profile(p).len(), 0)
```

</details>

#### refuses AllowHybrid from any mode other than resident_gpu

- refuses AllowHybrid from any mode other than resident_gpu


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses AllowHybrid from any mode other than resident_gpu")
val p = stage_execution_profile(ExecutionMode.HybridVectorGpu, true,
                                0, 0, 0, 0,
                                StageFallbackPolicy.AllowHybrid,
                                VerificationPolicy.Off,
                                DEVICE_BIT_CPU_SCALAR | DEVICE_BIT_GPU)
assert_false(profile_fallback_reachable(p))
assert_equal(encode_stage_execution_profile(p).len(), 0)
```

</details>

#### refuses an empty device mask

- refuses an empty device mask


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses an empty device mask")
val p = stage_execution_profile(ExecutionMode.CpuReference, true,
                                0, 0, 0, 0,
                                StageFallbackPolicy.Forbid,
                                VerificationPolicy.Off, 0)
assert_equal(encode_stage_execution_profile(p).len(), 0)
```

</details>

#### refuses a negative budget

- refuses a negative budget


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a negative budget")
val p = stage_execution_profile(ExecutionMode.CpuReference, true,
                                -1, 0, 0, 0,
                                StageFallbackPolicy.Forbid,
                                VerificationPolicy.Off,
                                DEVICE_BIT_CPU_SCALAR)
assert_false(profile_budgets_valid(p))
assert_equal(encode_stage_execution_profile(p).len(), 0)
```

</details>

#### detects memory-budget overflow by the sign of the sum, not a width constant

- detects memory-budget overflow by the sign of the sum, not a width constant


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects memory-budget overflow by the sign of the sum, not a width constant")
# The 32-bit trap that bit earlier waves: `a + b <= MAX` on two
# same-width unsigned fields wraps and passes. Two huge non-negative
# i64 budgets sum to a NEGATIVE i64, which is the overflow signal.
val big = 4611686018427387904
val p = stage_execution_profile(ExecutionMode.CpuReference, true,
                                big, big, 0, 0,
                                StageFallbackPolicy.Forbid,
                                VerificationPolicy.Off,
                                DEVICE_BIT_CPU_SCALAR)
assert_true(p.host_memory_budget + p.device_memory_budget < 0)
assert_false(profile_budgets_valid(p))
assert_equal(encode_stage_execution_profile(p).len(), 0)
```

</details>

#### refuses capabilities with an empty backend name

- refuses capabilities with an empty backend name


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses capabilities with an empty backend name")
val c = stage_capabilities("", MODE_BIT_CPU_REFERENCE, 0,
                           VerificationPolicy.Off, true,
                           DEVICE_BIT_CPU_SCALAR)
assert_false(stage_capabilities_valid(c))
assert_equal(encode_stage_capabilities(c).len(), 0)
```

</details>

#### refuses capabilities claiming cpu_reference without the scalar CPU bit

- refuses capabilities claiming cpu_reference without the scalar CPU bit


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses capabilities claiming cpu_reference without the scalar CPU bit")
val c = stage_capabilities("odd", MODE_BIT_CPU_REFERENCE, 0,
                           VerificationPolicy.Off, true,
                           DEVICE_BIT_GPU)
assert_false(stage_capabilities_encodable(c))
assert_equal(encode_stage_capabilities(c).len(), 0)
```

</details>

#### refuses a non-ASCII backend name

- refuses a non-ASCII backend name


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a non-ASCII backend name")
val c = stage_capabilities("gpü", MODE_BIT_CPU_REFERENCE, 0,
                           VerificationPolicy.Off, true,
                           DEVICE_BIT_CPU_SCALAR)
assert_equal(encode_stage_capabilities(c).len(), 0)
```

</details>

### three modes everywhere, and no silent fallback

#### keeps all three modes expressible with the same profile shape

- keeps all three modes expressible with the same profile shape


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps all three modes expressible with the same profile shape")
val cpu = stage_execution_profile_cpu_reference()
val hyb = stage_execution_profile(ExecutionMode.HybridVectorGpu, true,
                                  0, 0, 0, 0,
                                  StageFallbackPolicy.Forbid,
                                  VerificationPolicy.Off,
                                  DEVICE_BIT_CPU_SCALAR | DEVICE_BIT_GPU)
val res = fixture_resident_allow_hybrid()
assert_true(stage_execution_profile_valid(cpu))
assert_true(stage_execution_profile_valid(hyb))
assert_true(stage_execution_profile_valid(res))
assert_equal(execution_mode_to_u8(cpu.mode), 0)
assert_equal(execution_mode_to_u8(hyb.mode), 1)
assert_equal(execution_mode_to_u8(res.mode), 2)
```

</details>

#### makes an unsatisfiable request unrepresentable rather than degradable

- makes an unsatisfiable request unrepresentable rather than degradable


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("makes an unsatisfiable request unrepresentable rather than degradable")
# This is the whole guarantee: a profile that could only be honoured by
# running somewhere it did not ask for cannot be put on the wire, so it
# can never reach a backend and become an unexplained cpu_reference
# receipt.
val bad = stage_execution_profile(ExecutionMode.ResidentGpu, true,
                                  0, 0, 0, 0,
                                  StageFallbackPolicy.Forbid,
                                  VerificationPolicy.Off,
                                  DEVICE_BIT_CPU_SCALAR)
assert_false(profile_mode_device_consistent(bad))
assert_equal(encode_stage_execution_profile(bad).len(), 0)
```

</details>

#### requires the planner to raise when Forbid cannot be honoured

- requires the planner to raise when Forbid cannot be honoured


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires the planner to raise when Forbid cannot be honoured")
assert_true(profile_requires_error_on_unsatisfied(
    stage_execution_profile_cpu_reference()))
assert_false(profile_requires_error_on_unsatisfied(
    fixture_resident_allow_cpu()))
assert_false(profile_requires_error_on_unsatisfied(
    fixture_resident_allow_hybrid()))
```

</details>

#### walks the ladder one rung at a time

- walks the ladder one rung at a time


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("walks the ladder one rung at a time")
assert_equal(execution_mode_to_u8(profile_degradation_target(
                 fixture_resident_allow_hybrid())), 1)
assert_equal(execution_mode_to_u8(profile_degradation_target(
                 fixture_resident_allow_cpu())), 0)
```

</details>

#### reports no move available when degradation is forbidden

- reports no move available when degradation is forbidden


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports no move available when degradation is forbidden")
val p = stage_execution_profile_cpu_reference()
assert_equal(execution_mode_to_u8(profile_degradation_target(p)),
             execution_mode_to_u8(p.mode))
```

</details>

### capabilities decide satisfaction before a stage ever runs

#### accepts a resident request against a fully capable GPU backend

- accepts a resident request against a fully capable GPU backend


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts a resident request against a fully capable GPU backend")
assert_true(capabilities_satisfy_profile(fixture_caps_gpu(),
                                         fixture_resident_allow_cpu()))
```

</details>

#### refuses a resident request against a CPU-only backend

- refuses a resident request against a CPU-only backend


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a resident request against a CPU-only backend")
assert_false(capabilities_satisfy_profile(fixture_caps_cpu(),
                                          fixture_resident_allow_cpu()))
```

</details>

#### accepts the cpu_reference request every backend must serve

- accepts the cpu_reference request every backend must serve


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts the cpu_reference request every backend must serve")
assert_true(capabilities_satisfy_profile(
    fixture_caps_cpu(), stage_execution_profile_cpu_reference()))
assert_true(capabilities_satisfy_profile(
    fixture_caps_gpu(), stage_execution_profile_cpu_reference()))
```

</details>

#### refuses a verification level the backend cannot reach

- refuses a verification level the backend cannot reach


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a verification level the backend cannot reach")
val p = stage_execution_profile(ExecutionMode.CpuReference, true,
                                0, 0, 0, 0,
                                StageFallbackPolicy.Forbid,
                                VerificationPolicy.OracleCompare,
                                DEVICE_BIT_CPU_SCALAR)
assert_false(capabilities_satisfy_profile(fixture_caps_cpu(), p))
assert_true(capabilities_satisfy_profile(fixture_caps_gpu(), p))
```

</details>

#### refuses a deterministic request against a non-deterministic backend

- refuses a deterministic request against a non-deterministic backend


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a deterministic request against a non-deterministic backend")
val c = stage_capabilities("loose", MODE_BIT_CPU_REFERENCE, 0,
                           VerificationPolicy.DeterministicHash, false,
                           DEVICE_BIT_CPU_SCALAR)
assert_false(capabilities_satisfy_profile(
    c, stage_execution_profile_cpu_reference()))
```

</details>

#### never reports satisfaction for an invalid profile or capability

- never reports satisfaction for an invalid profile or capability


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("never reports satisfaction for an invalid profile or capability")
val bad = stage_execution_profile(ExecutionMode.ResidentGpu, true,
                                  0, 0, 0, 0,
                                  StageFallbackPolicy.Forbid,
                                  VerificationPolicy.Off,
                                  DEVICE_BIT_CPU_SCALAR)
assert_false(capabilities_satisfy_profile(fixture_caps_gpu(), bad))
```

</details>

### contract version is pinned

#### freezes this group at version 1

- freezes this group at version 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("freezes this group at version 1")
assert_equal(STRUCTURAL_EXECUTION_PROFILE_VERSION, 1)
assert_equal(stage_execution_profile_cpu_reference().contract_version, 1)
assert_equal(fixture_caps_gpu().contract_version, 1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/common/structural/execution_profile_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering device mask bit vocabulary, execution mode bit vocabulary, StageFallbackPolicy vocabulary, StorageCapabilityTier vocabulary, wire booleans, StageExecutionProfile encodes to the hand-derived golden bytes, StageCapabilities encodes to the hand-derived golden bytes, record magics are distinct, StageExecutionProfile round-trips, StageCapabilities round-trips, decode rejects malformed profile buffers, decode rejects malformed capabilities buffers, encode enforces the same invariants as decode, three modes everywhere, and no silent fallback, capabilities decide satisfaction before a stage ever runs, contract version is pinned.
- device mask bit vocabulary
- execution mode bit vocabulary
- StageFallbackPolicy vocabulary
- StorageCapabilityTier vocabulary
- wire booleans
- StageExecutionProfile encodes to the hand-derived golden bytes
- StageCapabilities encodes to the hand-derived golden bytes
- record magics are distinct
- StageExecutionProfile round-trips
- StageCapabilities round-trips
- decode rejects malformed profile buffers
- decode rejects malformed capabilities buffers
- encode enforces the same invariants as decode
- three modes everywhere, and no silent fallback
- capabilities decide satisfaction before a stage ever runs
- contract version is pinned

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 81 |
| Active scenarios | 81 |
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

- Canonical SPipe generation for source `4e8ca1f8e1e7744101eab0d8dde4a4fc87dd0acf755714783ac423f315b47489`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4e8ca1f8e1e7744101eab0d8dde4a4fc87dd0acf755714783ac423f315b47489`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4e8ca1f8e1e7744101eab0d8dde4a4fc87dd0acf755714783ac423f315b47489`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/common/structural/execution_profile_contract_spec.spl
mirror: doc/06_spec/01_unit/common/structural/execution_profile_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/common/structural/execution_profile_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/common/structural/execution_profile_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/common/structural/execution_profile_contract_spec.spl:190:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'assigns one bit per cost channel section 21.2 budgets separately' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/common/structural/execution_profile_contract_spec.spl:198:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'declares exactly four bits and no fifth' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/common/structural/execution_profile_contract_spec.spl:204:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a set reserved bit rather than ignoring it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
