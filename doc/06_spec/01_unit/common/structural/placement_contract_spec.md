# Placement Contract Specification

> Tests covering Placement contract version and record lengths, AccessPattern wire discriminants, PersistencePolicy wire discriminants, LeaseState wire discriminants, ResidencyTierSet wire slot, LeaseAccess rights, Unsigned 64-bit comparison, PlacementRequest exact bytes, LeaseGrant exact bytes, LeaseSet exact bytes, PlacementPlan exact bytes, Placement round trip, Lease validity rules, Encoder refuses to emit an ill-formed record, Decoder rejects malformed placement buffers, Bridge to the existing CostEstimate carrier.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 78 | 78 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Placement Contract Specification

## Scenarios

### Placement contract version and record lengths

#### ties the wire version to the already-frozen schema id

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- ties the wire version to the already-frozen schema id


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ties the wire version to the already-frozen schema id")
assert_equal(PLACE_SCHEMA_VERSION, 1)
assert_equal(PLACE_SCHEMA_VERSION, PLACEMENT_SCHEMA_ID)
```

</details>

#### freezes every record length

- freezes every record length


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("freezes every record length")
assert_equal(PLACEMENT_REQUEST_LEN, 82)
assert_equal(LEASE_GRANT_LEN, 32)
assert_equal(PLACEMENT_COST_LEN, 70)
assert_equal(PLACEMENT_PLAN_LEN, 142)
```

</details>

#### keeps a lease grant inside the 32-48 byte hot-descriptor budget

- keeps a lease grant inside the 32-48 byte hot-descriptor budget


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps a lease grant inside the 32-48 byte hot-descriptor budget")
assert_true(LEASE_GRANT_LEN >= 32 and LEASE_GRANT_LEN <= 48)
```

</details>

### AccessPattern wire discriminants

#### assigns declaration order as wire order

- assigns declaration order as wire order


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assigns declaration order as wire order")
assert_equal(ACCESS_PATTERN_MAX, 4)
assert_equal(ACCESS_PATTERN_COUNT, 5)
```

</details>

#### round-trips every valid discriminant

- round-trips every valid discriminant


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips every valid discriminant")
var v = 0
while v <= ACCESS_PATTERN_MAX:
    assert_equal(access_pattern_to_u8(access_pattern_from_u8(v)), v)
    assert_true(access_pattern_valid(v))
    v = v + 1
```

</details>

#### rejects a discriminant past the maximum

- rejects a discriminant past the maximum


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a discriminant past the maximum")
assert_false(access_pattern_valid(ACCESS_PATTERN_MAX + 1))
assert_false(access_pattern_valid(0 - 1))
```

</details>

### PersistencePolicy wire discriminants

#### round-trips every valid discriminant

- round-trips every valid discriminant


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips every valid discriminant")
assert_equal(PERSISTENCE_POLICY_MAX, 3)
assert_equal(PERSISTENCE_POLICY_COUNT, 4)
var v = 0
while v <= PERSISTENCE_POLICY_MAX:
    assert_equal(persistence_policy_to_u8(persistence_policy_from_u8(v)), v)
    v = v + 1
assert_false(persistence_policy_valid(PERSISTENCE_POLICY_MAX + 1))
```

</details>

### LeaseState wire discriminants

#### freezes the five derived states in order

- freezes the five derived states in order


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("freezes the five derived states in order")
assert_equal(LEASE_STATE_MAX, 4)
assert_equal(LEASE_STATE_COUNT, 5)
var v = 0
while v <= LEASE_STATE_MAX:
    assert_equal(lease_state_to_u8(lease_state_from_u8(v)), v)
    v = v + 1
assert_false(lease_state_valid(LEASE_STATE_MAX + 1))
```

</details>

#### splits live from dead exhaustively

- splits live from dead exhaustively


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("splits live from dead exhaustively")
var v = 0
while v <= LEASE_STATE_MAX:
    assert_true(lease_state_is_live(v) != lease_state_is_dead(v))
    v = v + 1
```

</details>

#### marks exactly Pinned and InFlight as eviction-preventing

- marks exactly Pinned and InFlight as eviction-preventing


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("marks exactly Pinned and InFlight as eviction-preventing")
assert_false(lease_state_prevents_eviction(0))
assert_true(lease_state_prevents_eviction(1))
assert_true(lease_state_prevents_eviction(2))
assert_false(lease_state_prevents_eviction(3))
assert_false(lease_state_prevents_eviction(4))
```

</details>

### ResidencyTierSet wire slot

#### assigns bit i to tier discriminant i

- assigns bit i to tier discriminant i


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assigns bit i to tier discriminant i")
assert_equal(TIER_SET_DEVICE_LOCAL, 1)
assert_equal(TIER_SET_DEVICE_SHARED, 2)
assert_equal(TIER_SET_HOST_PINNED, 4)
assert_equal(TIER_SET_HOST_HOT, 8)
assert_equal(TIER_SET_HOST_COLD, 16)
assert_equal(TIER_SET_SSD_CAS, 32)
assert_equal(TIER_SET_RECOMPUTABLE, 64)
assert_equal(TIER_SET_KNOWN, 127)
assert_equal(RESIDENCY_TIER_COUNT, 7)
```

</details>

#### hard-rejects a reserved bit instead of masking it away

- hard-rejects a reserved bit instead of masking it away


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hard-rejects a reserved bit instead of masking it away")
assert_true(tier_set_valid(TIER_SET_KNOWN))
assert_false(tier_set_valid(128))
assert_false(tier_set_valid(TIER_SET_KNOWN + 1))
```

</details>

#### derives the device tiers from the frozen schema helper

- derives the device tiers from the frozen schema helper


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("derives the device tiers from the frozen schema helper")
assert_equal(TIER_SET_DEVICE, 3)
assert_true(tier_set_has_device(TIER_SET_DEVICE_LOCAL))
assert_true(tier_set_has_device(TIER_SET_DEVICE_SHARED))
assert_false(tier_set_has_device(TIER_SET_HOST_HOT))
assert_false(tier_set_has_device(TIER_SET_SSD_CAS))
```

</details>

### LeaseAccess rights

#### freezes read and write with the rest reserved

- freezes read and write with the rest reserved


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("freezes read and write with the rest reserved")
assert_equal(LEASE_ACCESS_NONE, 0)
assert_equal(LEASE_ACCESS_READ, 1)
assert_equal(LEASE_ACCESS_WRITE, 2)
assert_equal(LEASE_ACCESS_KNOWN, 3)
assert_false(lease_access_valid(4))
```

</details>

#### maps each AccessPattern to the rights it implies

- maps each AccessPattern to the rights it implies


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps each AccessPattern to the rights it implies")
assert_equal(access_pattern_required_rights(0), LEASE_ACCESS_READ)
assert_equal(access_pattern_required_rights(1), LEASE_ACCESS_READ)
assert_equal(access_pattern_required_rights(2), LEASE_ACCESS_KNOWN)
assert_equal(access_pattern_required_rights(3), LEASE_ACCESS_KNOWN)
assert_equal(access_pattern_required_rights(4), LEASE_ACCESS_WRITE)
```

</details>

#### refuses an under-privileged grant

- refuses an under-privileged grant


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses an under-privileged grant")
assert_true(lease_access_satisfies(LEASE_ACCESS_KNOWN, LEASE_ACCESS_WRITE))
assert_false(lease_access_satisfies(LEASE_ACCESS_READ, LEASE_ACCESS_WRITE))
assert_false(lease_access_satisfies(LEASE_ACCESS_NONE, LEASE_ACCESS_READ))
```

</details>

### Unsigned 64-bit comparison

#### orders a high u64 above a low one even though it decodes negative

- orders a high u64 above a low one even though it decodes negative


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("orders a high u64 above a low one even though it decodes negative")
assert_true(U64_MSB_BITS < 0)
assert_true(place_u64_lt(1, U64_MSB_BITS))
assert_false(place_u64_lt(U64_MSB_BITS, 1))
assert_true(place_u64_lt(U64_MSB_BITS, U64_MAX_BITS))
assert_true(place_u64_le(U64_MAX_BITS, U64_MAX_BITS))
```

</details>

<details>
<summary>Advanced: computes remaining room instead of a sum that would wrap</summary>

#### computes remaining room instead of a sum that would wrap

- computes remaining room instead of a sum that would wrap


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes remaining room instead of a sum that would wrap")
assert_true(place_u64_add_fits(0, U64_MAX_BITS))
assert_true(place_u64_add_fits(ADDR_TOP, 0xffff))
assert_false(place_u64_add_fits(ADDR_TOP, 0x10000))
assert_false(place_u64_add_fits(U64_MAX_BITS, 1))
```

</details>


</details>

### PlacementRequest exact bytes

#### encodes the minimal request to the golden vector

- encodes the minimal request to the golden vector


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes the minimal request to the golden vector")
assert_equal(wire_to_hex(encode_placement_request(minimal_request())),
             GOLDEN_REQUEST_MINIMAL)
```

</details>

#### encodes the fully populated request to the golden vector

- encodes the fully populated request to the golden vector


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes the fully populated request to the golden vector")
assert_equal(wire_to_hex(encode_placement_request(full_request())),
             GOLDEN_REQUEST_FULL)
```

</details>

#### encodes an interval only an unsigned comparison accepts

- encodes an interval only an unsigned comparison accepts


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes an interval only an unsigned comparison accepts")
assert_equal(
    wire_to_hex(encode_placement_request(unsigned_epoch_request())),
    GOLDEN_REQUEST_UNSIGNED_EPOCH)
```

</details>

#### fills unused preference slots with 0xff, never 0

- fills unused preference slots with 0xff, never 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fills unused preference slots with 0xff, never 0")
assert_equal(PLACE_NO_TIER, 255)
val bytes = encode_placement_request(minimal_request())
assert_equal(bytes[8 + 11] & 0xFF, 255)
assert_equal(bytes[8 + 17] & 0xFF, 255)
```

</details>

#### emits exactly the frozen record length

- emits exactly the frozen record length


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits exactly the frozen record length")
assert_equal(encode_placement_request(minimal_request()).len(),
             8 + PLACEMENT_REQUEST_LEN)
```

</details>

### LeaseGrant exact bytes

#### encodes an active lease to the golden vector

- encodes an active lease to the golden vector


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes an active lease to the golden vector")
assert_equal(wire_to_hex(encode_lease_grant(lease_active())),
             GOLDEN_LEASE_ACTIVE)
```

</details>

#### encodes the maximum non-wrapping window to the golden vector

- encodes the maximum non-wrapping window to the golden vector


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes the maximum non-wrapping window to the golden vector")
assert_equal(wire_to_hex(encode_lease_grant(lease_pinned_max())),
             GOLDEN_LEASE_PINNED_MAX)
```

</details>

#### encodes a revoked lease to its single legal shape

- encodes a revoked lease to its single legal shape


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes a revoked lease to its single legal shape")
assert_equal(wire_to_hex(encode_lease_grant(lease_revoked())),
             GOLDEN_LEASE_REVOKED)
```

</details>

#### emits exactly the frozen record length

- emits exactly the frozen record length


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits exactly the frozen record length")
assert_equal(encode_lease_grant(lease_active()).len(),
             8 + LEASE_GRANT_LEN)
```

</details>

### LeaseSet exact bytes

#### encodes an empty acquire result to the golden vector

- encodes an empty acquire result to the golden vector


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes an empty acquire result to the golden vector")
assert_equal(wire_to_hex(encode_lease_set(lease_set_wire([]))),
             GOLDEN_LEASE_SET_EMPTY)
```

</details>

#### encodes an ordered pair to the golden vector

- encodes an ordered pair to the golden vector


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes an ordered pair to the golden vector")
assert_equal(wire_to_hex(encode_lease_set(lease_set_pair())),
             GOLDEN_LEASE_SET_PAIR)
```

</details>

### PlacementPlan exact bytes

#### encodes the minimal acquirable plan to the golden vector

- encodes the minimal acquirable plan to the golden vector


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes the minimal acquirable plan to the golden vector")
assert_equal(wire_to_hex(encode_placement_plan(minimal_plan())),
             GOLDEN_PLAN_MINIMAL)
```

</details>

#### encodes a fully populated plan to the golden vector

- encodes a fully populated plan to the golden vector


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes a fully populated plan to the golden vector")
assert_equal(wire_to_hex(encode_placement_plan(full_plan())),
             GOLDEN_PLAN_FULL)
```

</details>

#### emits exactly the frozen record length

- emits exactly the frozen record length


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits exactly the frozen record length")
assert_equal(encode_placement_plan(minimal_plan()).len(),
             8 + PLACEMENT_PLAN_LEN)
```

</details>

### Placement round trip

#### reconstructs every request shape

- reconstructs every request shape


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reconstructs every request shape")
val a = decode_placement_request(encode_placement_request(minimal_request()))
assert_true(a.ok)
assert_true(placement_request_equal(a.value, minimal_request()))
val b = decode_placement_request(encode_placement_request(full_request()))
assert_true(b.ok)
assert_true(placement_request_equal(b.value, full_request()))
val c = decode_placement_request(
    encode_placement_request(unsigned_epoch_request()))
assert_true(c.ok)
assert_true(placement_request_equal(c.value, unsigned_epoch_request()))
```

</details>

#### preserves the preference ORDER, not just the membership

- preserves the preference ORDER, not just the membership


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves the preference ORDER, not just the membership")
val r = decode_placement_request(encode_placement_request(full_request()))
assert_true(r.ok)
assert_equal(r.value.preferred.len(), 3)
assert_equal(r.value.preferred[0], 0)
assert_equal(r.value.preferred[1], 2)
assert_equal(r.value.preferred[2], 1)
```

</details>

#### reconstructs every lease grant shape

- reconstructs every lease grant shape


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reconstructs every lease grant shape")
val a = decode_lease_grant(encode_lease_grant(lease_active()))
assert_true(a.ok)
assert_equal(a.value.device_address, 0x00007f0000001000)
assert_equal(a.value.lease_epoch, 257)
val b = decode_lease_grant(encode_lease_grant(lease_pinned_max()))
assert_true(b.ok)
assert_equal(b.value.device_address, ADDR_TOP)
assert_equal(b.value.length, 0xffff)
val c = decode_lease_grant(encode_lease_grant(lease_revoked()))
assert_true(c.ok)
assert_equal(c.value.lease_epoch, PLACEMENT_NO_EPOCH)
assert_equal(c.value.device_address, 0)
```

</details>

#### reconstructs a lease set

- reconstructs a lease set


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reconstructs a lease set")
val s = decode_lease_set(encode_lease_set(lease_set_pair()))
assert_true(s.ok)
assert_equal(s.value.grants.len(), 2)
assert_equal(s.value.grants[0].object_slot, 5)
assert_equal(s.value.grants[1].object_slot, 0xfffffffe)
```

</details>

#### reconstructs every plan shape

- reconstructs every plan shape


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reconstructs every plan shape")
val a = decode_placement_plan(encode_placement_plan(minimal_plan()))
assert_true(a.ok)
assert_true(placement_plan_equal(a.value, minimal_plan()))
val b = decode_placement_plan(encode_placement_plan(full_plan()))
assert_true(b.ok)
assert_true(placement_plan_equal(b.value, full_plan()))
assert_equal(b.value.cost.confidence_milli, PLACE_CONFIDENCE_MAX)
```

</details>

### Lease validity rules

#### authorises a dereference only inside the granted epoch

- authorises a dereference only inside the granted epoch


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("authorises a dereference only inside the granted epoch")
val g = lease_active()
assert_true(lease_grant_valid_at(g, 257))
assert_false(lease_grant_valid_at(g, 258))
assert_false(lease_grant_valid_at(g, 256))
assert_false(lease_grant_valid_at(g, PLACEMENT_NO_EPOCH))
```

</details>

#### never authorises a dereference under a dead lease

- never authorises a dereference under a dead lease


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("never authorises a dereference under a dead lease")
assert_false(lease_grant_valid_at(lease_revoked(), PLACEMENT_NO_EPOCH))
assert_false(lease_grant_valid_at(lease_grant_dead(5, 9, 3, 0), 0))
```

</details>

#### bounds a resident view to the lease window

- bounds a resident view to the lease window


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bounds a resident view to the lease window")
val g = lease_active()
assert_true(lease_grant_covers(g, 0x00007f0000001000, 4096))
assert_true(lease_grant_covers(g, 0x00007f0000001010, 16))
assert_false(lease_grant_covers(g, 0x00007f0000000fff, 1))
assert_false(lease_grant_covers(g, 0x00007f0000001000, 4097))
assert_false(lease_grant_covers(g, 0x00007f0000002000, 1))
```

</details>

#### refuses a candidate range whose own length would wrap

- refuses a candidate range whose own length would wrap


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a candidate range whose own length would wrap")
val g = lease_pinned_max()
assert_true(lease_grant_covers(g, ADDR_TOP, 0xffff))
assert_false(lease_grant_covers(g, ADDR_TOP, 0x10000))
```

</details>

#### validates a ResidentView against its grant, epoch and window

- validates a ResidentView against its grant, epoch and window


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates a ResidentView against its grant, epoch and window")
val g = lease_active()
assert_true(resident_view_valid_under(
    resident_view_wire(0x00007f0000001000, 4096, 5, 257), g))
assert_false(resident_view_valid_under(
    resident_view_wire(0x00007f0000001000, 4096, 5, 258), g))
assert_false(resident_view_valid_under(
    resident_view_wire(0x00007f0000001000, 4096, 6, 257), g))
assert_false(resident_view_valid_under(
    resident_view_wire(0x00007f0000009000, 4096, 5, 257), g))
assert_false(resident_view_valid_under(
    resident_view_wire(0, 0, 5, PLACEMENT_NO_EPOCH), lease_revoked()))
```

</details>

#### makes an EntityRef's validity a decidable question

- makes an EntityRef's validity a decidable question


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("makes an EntityRef's validity a decidable question")
val g = lease_active()
assert_true(entity_ref_valid_under(5, 257, g))
assert_false(entity_ref_valid_under(5, 258, g))
assert_false(entity_ref_valid_under(6, 257, g))
assert_false(entity_ref_valid_under(5, PLACEMENT_NO_EPOCH, lease_revoked()))
```

</details>

#### checks a grant against the request it answers

- checks a grant against the request it answers


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks a grant against the request it answers")
val r = full_request()
assert_true(lease_grant_satisfies_request(
    lease_grant(0x11223344, 7, 1, 0, 3, 0, 0x1000, 0x1000), r))
# tier HostHot(3) is not in the request's required set {0,1,2}
assert_false(lease_grant_satisfies_request(
    lease_grant(0x11223344, 7, 1, 0, 3, 3, 0x1000, 0x1000), r))
# read-only grant for a ReadWrite request
assert_false(lease_grant_satisfies_request(
    lease_grant(0x11223344, 7, 1, 0, 1, 0, 0x1000, 0x1000), r))
# right object slot, wrong generation
assert_false(lease_grant_satisfies_request(
    lease_grant(0x11223344, 8, 1, 0, 3, 0, 0x1000, 0x1000), r))
```

</details>

#### relates a plan to the lease set acquired from it

- relates a plan to the lease set acquired from it


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("relates a plan to the lease set acquired from it")
assert_true(lease_set_acquirable_from(minimal_plan(), lease_set_pair()))
# an acquire that returns an already-revoked grant is not a success
val dead: [LeaseGrant] = [lease_revoked()]
assert_false(lease_set_acquirable_from(minimal_plan(),
                                       lease_set_wire(dead)))
assert_false(lease_set_acquirable_from(minimal_plan(),
                                       lease_set_wire([])))
```

</details>

#### finds a grant by slot and returns an unusable miss

- finds a grant by slot and returns an unusable miss


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds a grant by slot and returns an unusable miss")
val s = lease_set_pair()
assert_equal(lease_set_lookup(s, 5).lease_epoch, 257)
assert_false(lease_grant_well_formed(lease_set_lookup(s, 77)))
```

</details>

### Encoder refuses to emit an ill-formed record

#### cannot write a dead lease carrying a live address

- cannot write a dead lease carrying a live address


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cannot write a dead lease carrying a live address")
assert_equal(encode_lease_grant(
    lease_grant(5, 9, PLACEMENT_NO_EPOCH, 4, 0, 0, 0x1000, 0x1000)).len(), 0)
assert_equal(encode_lease_grant(
    lease_grant(5, 9, 7, 4, 0, 0, 0, 0)).len(), 0)
assert_equal(encode_lease_grant(
    lease_grant(5, 9, PLACEMENT_NO_EPOCH, 3, 1, 0, 0, 0)).len(), 0)
```

</details>

#### cannot write a live lease with no epoch, no rights or no window

- cannot write a live lease with no epoch, no rights or no window


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cannot write a live lease with no epoch, no rights or no window")
assert_equal(encode_lease_grant(
    lease_grant(5, 9, PLACEMENT_NO_EPOCH, 0, 3, 0, 0x1000, 0x1000)).len(), 0)
assert_equal(encode_lease_grant(
    lease_grant(5, 9, 7, 0, 0, 0, 0x1000, 0x1000)).len(), 0)
assert_equal(encode_lease_grant(
    lease_grant(5, 9, 7, 0, 3, 0, 0, 0x1000)).len(), 0)
assert_equal(encode_lease_grant(
    lease_grant(5, 9, 7, 0, 3, 0, 0x1000, 0)).len(), 0)
```

</details>

#### cannot write a lease window that wraps past 2^64

- cannot write a lease window that wraps past 2^64


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cannot write a lease window that wraps past 2^64")
assert_equal(encode_lease_grant(
    lease_grant(5, 9, 7, 0, 3, 0, ADDR_TOP, 0x10000)).len(), 0)
```

</details>

#### cannot write an out-of-order or duplicated lease set

- cannot write an out-of-order or duplicated lease set


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cannot write an out-of-order or duplicated lease set")
val swapped: [LeaseGrant] = [lease_pinned_max(), lease_active()]
assert_equal(encode_lease_set(lease_set_wire(swapped)).len(), 0)
val dup: [LeaseGrant] = [lease_active(), lease_active()]
assert_equal(encode_lease_set(lease_set_wire(dup)).len(), 0)
```

</details>

#### cannot write a request with an empty or reserved tier set

- cannot write a request with an empty or reserved tier set


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cannot write a request with an empty or reserved tier set")
val none: [i64] = []
assert_equal(encode_placement_request(
    placement_request_wire(1, 1, 0, 0, none, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0)).len(), 0)
assert_equal(encode_placement_request(
    placement_request_wire(1, 1, 0, 128, none, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0)).len(), 0)
```

</details>

#### cannot write a preference outside the required set or duplicated

- cannot write a preference outside the required set or duplicated


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cannot write a preference outside the required set or duplicated")
val outside: [i64] = [4]
assert_equal(encode_placement_request(
    placement_request_wire(1, 1, 0, 8, outside, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0)).len(), 0)
val dup: [i64] = [3, 3]
assert_equal(encode_placement_request(
    placement_request_wire(1, 1, 0, 8, dup, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0)).len(), 0)
```

</details>

#### cannot write a device tier requirement without the GPU bit

- cannot write a device tier requirement without the GPU bit


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cannot write a device tier requirement without the GPU bit")
# DeviceLocal required, but the mask permits only CPU-scalar. Uses the
# EXEC lane's frozen DeviceMask vocabulary, not a second one.
val none: [i64] = []
assert_equal(encode_placement_request(
    placement_request_wire(1, 1, 0, 1, none, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0)).len(), 0)
assert_true(encode_placement_request(
    placement_request_wire(1, 1, 0, 1, none, 0, 0, 0, 0, DEVICE_BIT_GPU,
                           0, 0, 0, 0, 0)).len() > 0)
```

</details>

#### cannot write a device_mask of zero or one with a reserved bit

- cannot write a device_mask of zero or one with a reserved bit


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cannot write a device_mask of zero or one with a reserved bit")
val none: [i64] = []
assert_false(device_mask_valid(0))
assert_false(device_mask_valid(16))
assert_true(device_mask_valid(DEVICE_MASK_KNOWN))
assert_equal(encode_placement_request(
    placement_request_wire(1, 1, 0, 8, none, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)).len(), 0)
assert_equal(encode_placement_request(
    placement_request_wire(1, 1, 0, 8, none, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0)).len(), 0)
```

</details>

#### cannot write an inverted liveness interval

- cannot write an inverted liveness interval


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cannot write an inverted liveness interval")
val none: [i64] = []
assert_equal(encode_placement_request(
    placement_request_wire(1, 1, 0, 8, none, 0, 0, 0, 0, 1, 9, 8, 0, 0, 0)).len(), 0)
```

</details>

#### cannot write an absent deadline that still carries a timestamp

- cannot write an absent deadline that still carries a timestamp


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cannot write an absent deadline that still carries a timestamp")
val none: [i64] = []
assert_equal(encode_placement_request(
    placement_request_wire(1, 1, 0, 8, none, 0, 0, 5, 0, 1, 0, 0, 0, 0, 0)).len(), 0)
```

</details>

#### cannot write a plan without a lease arena

- cannot write a plan without a lease arena


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cannot write a plan without a lease arena")
assert_equal(encode_placement_plan(
    placement_plan_wire(PLACEMENT_NO_SLOT, 0, PLACEMENT_NO_SLOT, 0,
                        PLACEMENT_NO_SLOT, 0, PLACEMENT_NO_SLOT, 0,
                        PLACEMENT_NO_SLOT, 0, placement_cost_zero(),
                        PLACE_ZERO_SEED)).len(), 0)
```

</details>

#### cannot write an absent arena sentinel carrying a generation

- cannot write an absent arena sentinel carrying a generation


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cannot write an absent arena sentinel carrying a generation")
assert_equal(encode_placement_plan(
    placement_plan_wire(PLACEMENT_NO_SLOT, 4, PLACEMENT_NO_SLOT, 0,
                        PLACEMENT_NO_SLOT, 0, PLACEMENT_NO_SLOT, 0,
                        3, 1, placement_cost_zero(),
                        PLACE_ZERO_SEED)).len(), 0)
```

</details>

#### cannot write a confidence above 1000 per-mille or a bad seed

- cannot write a confidence above 1000 per-mille or a bad seed


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cannot write a confidence above 1000 per-mille or a bad seed")
val over = placement_cost_wire(0, 0, 0, 0, 0, 0, 0, 0, 0, 1001)
assert_false(placement_cost_well_formed(over))
assert_equal(encode_placement_plan(
    placement_plan_wire(PLACEMENT_NO_SLOT, 0, PLACEMENT_NO_SLOT, 0,
                        PLACEMENT_NO_SLOT, 0, PLACEMENT_NO_SLOT, 0,
                        3, 1, over, PLACE_ZERO_SEED)).len(), 0)
assert_false(place_hex64_valid("ABCD"))
assert_false(place_hex64_valid(
    "0123456789ABCDEF0123456789abcdef0123456789abcdef0123456789abcdef"))
assert_true(place_hex64_valid(PLACE_ZERO_SEED))
```

</details>

### Decoder rejects malformed placement buffers

#### rejects an empty buffer, which is what a refused encode returns

- rejects an empty buffer, which is what a refused encode returns


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an empty buffer, which is what a refused encode returns")
val empty: [u8] = []
assert_false(decode_lease_grant(empty).ok)
assert_false(decode_placement_request(empty).ok)
assert_false(decode_placement_plan(empty).ok)
assert_false(decode_lease_set(empty).ok)
```

</details>

#### rejects a wrong schema version rather than negotiating it

- rejects a wrong schema version rather than negotiating it


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a wrong schema version rather than negotiating it")
assert_false(decode_lease_grant(
    corrupt_byte(encode_lease_grant(lease_active()), 4, 2)).ok)
assert_false(decode_placement_plan(
    corrupt_byte(encode_placement_plan(minimal_plan()), 4, 2)).ok)
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
assert_false(decode_lease_grant(
    corrupt_byte(encode_lease_grant(lease_active()), 6, 1)).ok)
```

</details>

#### rejects a cross-typed buffer

- rejects a cross-typed buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a cross-typed buffer")
assert_false(decode_lease_grant(encode_placement_plan(minimal_plan())).ok)
assert_false(decode_placement_plan(encode_lease_grant(lease_active())).ok)
assert_false(decode_placement_request(encode_lease_grant(lease_active())).ok)
assert_false(decode_lease_set(encode_lease_grant(lease_active())).ok)
```

</details>

#### rejects a truncated or over-long buffer

- rejects a truncated or over-long buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a truncated or over-long buffer")
val g = encode_lease_grant(lease_active())
assert_false(decode_lease_grant(truncated(g, g.len() - 1)).ok)
assert_false(decode_lease_grant(appended(g, 0)).ok)
val p = encode_placement_plan(full_plan())
assert_false(decode_placement_plan(truncated(p, p.len() - 1)).ok)
assert_false(decode_placement_plan(appended(p, 0)).ok)
```

</details>

#### rejects an unknown LeaseState discriminant, never defaults it

- rejects an unknown LeaseState discriminant, never defaults it


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an unknown LeaseState discriminant, never defaults it")
assert_false(decode_lease_grant(
    corrupt_byte(encode_lease_grant(lease_active()), 8 + 12, 5)).ok)
```

</details>

#### rejects a reserved LeaseAccess bit

- rejects a reserved LeaseAccess bit


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a reserved LeaseAccess bit")
assert_false(decode_lease_grant(
    corrupt_byte(encode_lease_grant(lease_active()), 8 + 13, 4)).ok)
```

</details>

#### rejects an unknown ResidencyTier discriminant

- rejects an unknown ResidencyTier discriminant


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an unknown ResidencyTier discriminant")
assert_false(decode_lease_grant(
    corrupt_byte(encode_lease_grant(lease_active()), 8 + 14, 7)).ok)
```

</details>

#### rejects a non-zero LeaseGrant reserved byte

- rejects a non-zero LeaseGrant reserved byte


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a non-zero LeaseGrant reserved byte")
assert_false(decode_lease_grant(
    corrupt_byte(encode_lease_grant(lease_active()), 8 + 15, 1)).ok)
```

</details>

#### rejects a decoded grant flipped to a dead state with a live address

- rejects a decoded grant flipped to a dead state with a live address


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a decoded grant flipped to a dead state with a live address")
# Byte 8+12 is `state`. Flipping Active(0) to Revoked(4) leaves the
# epoch and address in place, which is exactly the stale-lease shape.
assert_false(decode_lease_grant(
    corrupt_byte(encode_lease_grant(lease_active()), 8 + 12, 4)).ok)
```

</details>

#### rejects an unknown AccessPattern or PersistencePolicy in a request

- rejects an unknown AccessPattern or PersistencePolicy in a request


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an unknown AccessPattern or PersistencePolicy in a request")
val r = encode_placement_request(minimal_request())
assert_false(decode_placement_request(corrupt_byte(r, 8 + 8, 5)).ok)
assert_false(decode_placement_request(corrupt_byte(r, 8 + 18, 4)).ok)
```

</details>

#### rejects a reserved tier bit and a non-zero request reserved u16

- rejects a reserved tier bit and a non-zero request reserved u16


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a reserved tier bit and a non-zero request reserved u16")
val r = encode_placement_request(minimal_request())
assert_false(decode_placement_request(corrupt_byte(r, 8 + 9, 128)).ok)
assert_false(decode_placement_request(corrupt_byte(r, 8 + 20, 1)).ok)
```

</details>

#### rejects a reserved DeviceMask bit in a decoded request

- rejects a reserved DeviceMask bit in a decoded request


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a reserved DeviceMask bit in a decoded request")
# Byte 8+26 is the low byte of device_mask. 16 is the first reserved bit.
val r = encode_placement_request(minimal_request())
assert_false(decode_placement_request(corrupt_byte(r, 8 + 26, 16)).ok)
assert_false(decode_placement_request(corrupt_byte(r, 8 + 26, 0)).ok)
```

</details>

#### rejects preference filler that is not the 0xff sentinel

- rejects preference filler that is not the 0xff sentinel


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects preference filler that is not the 0xff sentinel")
val r = encode_placement_request(minimal_request())
assert_false(decode_placement_request(corrupt_byte(r, 8 + 11, 0)).ok)
assert_false(decode_placement_request(corrupt_byte(r, 8 + 17, 3)).ok)
```

</details>

#### rejects a preference length past the seven-tier bound

- rejects a preference length past the seven-tier bound


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a preference length past the seven-tier bound")
val r = encode_placement_request(minimal_request())
assert_false(decode_placement_request(corrupt_byte(r, 8 + 10, 8)).ok)
```

</details>

#### rejects a declared lease count larger than the buffer

- rejects a declared lease count larger than the buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a declared lease count larger than the buffer")
val s = encode_lease_set(lease_set_pair())
assert_false(decode_lease_set(corrupt_byte(s, 8, 9)).ok)
assert_false(decode_lease_set(corrupt_byte(s, 8, 1)).ok)
```

</details>

#### rejects a plan whose lease arena slot is the absent sentinel

- rejects a plan whose lease arena slot is the absent sentinel


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a plan whose lease arena slot is the absent sentinel")
# All FOUR bytes of the u32 must be 0xff to spell PLACEMENT_NO_SLOT;
# one 0xff byte is the ordinary slot 255 and must still decode.
val p = encode_placement_plan(minimal_plan())
assert_true(decode_placement_plan(corrupt_byte(p, 8 + 32, 255)).ok)
var q = corrupt_byte(p, 8 + 32, 255)
q = corrupt_byte(q, 8 + 33, 255)
q = corrupt_byte(q, 8 + 34, 255)
q = corrupt_byte(q, 8 + 35, 255)
assert_false(decode_placement_plan(q).ok)
```

</details>

#### rejects a plan confidence above 1000 per-mille

- rejects a plan confidence above 1000 per-mille


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a plan confidence above 1000 per-mille")
# Byte 8+40+68 is the low byte of confidence_milli; 0xe9 makes it 1001.
val p = encode_placement_plan(full_plan())
assert_false(decode_placement_plan(corrupt_byte(p, 8 + 40 + 68, 233)).ok)
```

</details>

### Bridge to the existing CostEstimate carrier

#### flattens the semantic CostEstimate without redeclaring it

- flattens the semantic CostEstimate without redeclaring it


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flattens the semantic CostEstimate without redeclaring it")
val c = CostEstimate(cpu_work: 1, simd_work: 2, gpu_work: 3,
                     host_to_device_bytes: 4, device_to_host_bytes: 5,
                     ssd_read_bytes: 6, ssd_write_bytes: 7,
                     synchronization_points: 8,
                     predicted_latency_us: 9, confidence_milli: 1000)
val w = placement_cost_from_estimate(c)
assert_true(placement_cost_equal(
    w, placement_cost_wire(1, 2, 3, 4, 5, 6, 7, 8, 9, 1000)))
assert_true(placement_cost_well_formed(w))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/common/structural/placement_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Placement contract version and record lengths, AccessPattern wire discriminants, PersistencePolicy wire discriminants, LeaseState wire discriminants, ResidencyTierSet wire slot, LeaseAccess rights, Unsigned 64-bit comparison, PlacementRequest exact bytes, LeaseGrant exact bytes, LeaseSet exact bytes, PlacementPlan exact bytes, Placement round trip, Lease validity rules, Encoder refuses to emit an ill-formed record, Decoder rejects malformed placement buffers, Bridge to the existing CostEstimate carrier.
- Placement contract version and record lengths
- AccessPattern wire discriminants
- PersistencePolicy wire discriminants
- LeaseState wire discriminants
- ResidencyTierSet wire slot
- LeaseAccess rights
- Unsigned 64-bit comparison
- PlacementRequest exact bytes
- LeaseGrant exact bytes
- LeaseSet exact bytes
- PlacementPlan exact bytes
- Placement round trip
- Lease validity rules
- Encoder refuses to emit an ill-formed record
- Decoder rejects malformed placement buffers
- Bridge to the existing CostEstimate carrier

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 78 |
| Active scenarios | 78 |
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

- Canonical SPipe generation for source `2812b6a734f9f5daa354bc711d9d9085e8b740ce96db23f092343dfcb801ab8e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2812b6a734f9f5daa354bc711d9d9085e8b740ce96db23f092343dfcb801ab8e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2812b6a734f9f5daa354bc711d9d9085e8b740ce96db23f092343dfcb801ab8e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/common/structural/placement_contract_spec.spl
mirror: doc/06_spec/01_unit/common/structural/placement_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/common/structural/placement_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/common/structural/placement_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/common/structural/placement_contract_spec.spl:241:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ties the wire version to the already-frozen schema id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/common/structural/placement_contract_spec.spl:247:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'freezes every record length' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/common/structural/placement_contract_spec.spl:255:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps a lease grant inside the 32-48 byte hot-descriptor budget' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
