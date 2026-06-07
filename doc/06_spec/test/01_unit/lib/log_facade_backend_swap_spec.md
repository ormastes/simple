# log_facade_backend_swap_spec

> log-lib-drivers Phase 4 spec — runtime backend swap, slot table, removal.

<!-- sdn-diagram:id=log_facade_backend_swap_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=log_facade_backend_swap_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

log_facade_backend_swap_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=log_facade_backend_swap_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# log_facade_backend_swap_spec

log-lib-drivers Phase 4 spec — runtime backend swap, slot table, removal.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/log_facade_backend_swap_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

log-lib-drivers Phase 4 spec — runtime backend swap, slot table, removal.

Covers AC-3 (sink swappable at runtime without modifying call sites) and
AC-6b (backend swap at runtime).

Status: RED PHASE. `std.log.facade` slot table not implemented yet.

Phase 3 contract (locked, §B + §H):
  - Up to 4 backend slots
  - log_register_backend(ops: LogBackendOps) -> Result<BackendId, Err>
  - log_remove_backend(id: BackendId) -> bool
  - log_set_backend(id, ops) — atomic swap
  - LogBackendOps shape mirrors DriverOps (no dyn, no vtable):
      { self_ptr, write_fn, write_record_fn, flush_fn, panic_mode_fn, kind, name }

## Scenarios

### log facade — backend registration (AC-3, AC-6b)

#### AC-6b: register a RingBufferBackend and emit 3 records — all visible

1. log set level
2. ring backend clear
3. log info
4. log info
5. log info
   - Expected: ring_backend_count(sink) equals `3`
6. log remove backend


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
log_set_level(LOG_INFO)
val sink = ring_backend_new(64)
val id = log_register_backend(sink.ops)
expect(id).to_be_greater_than(-1)
ring_backend_clear(sink)
# Act
log_info(SUBSYS_KERN, "one")
log_info(SUBSYS_KERN, "two")
log_info(SUBSYS_KERN, "three")
# Assert
expect(ring_backend_count(sink)).to_equal(3)
log_remove_backend(id)
```

</details>

#### AC-6b: swap backend — old keeps its 3, new gets the next emissions

1. log set level
2. ring backend clear
3. log info
4. log info
5. log info
   - Expected: ring_backend_count(sink_a) equals `3`
6. log remove backend
7. ring backend clear
8. log info
9. log info
   - Expected: ring_backend_count(sink_a) equals `3`
   - Expected: ring_backend_count(sink_b) equals `2`
10. log remove backend


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
log_set_level(LOG_INFO)
val sink_a = ring_backend_new(64)
val id_a = log_register_backend(sink_a.ops)
ring_backend_clear(sink_a)
log_info(SUBSYS_KERN, "a-1")
log_info(SUBSYS_KERN, "a-2")
log_info(SUBSYS_KERN, "a-3")
expect(ring_backend_count(sink_a)).to_equal(3)
# Swap: remove A, register B
log_remove_backend(id_a)
val sink_b = ring_backend_new(64)
val id_b = log_register_backend(sink_b.ops)
ring_backend_clear(sink_b)
log_info(SUBSYS_KERN, "b-1")
log_info(SUBSYS_KERN, "b-2")
# A frozen at 3, B sees the 2 new ones.
expect(ring_backend_count(sink_a)).to_equal(3)
expect(ring_backend_count(sink_b)).to_equal(2)
log_remove_backend(id_b)
```

</details>

### log facade — slot capacity (AC-3)

#### AC-3: MAX_BACKENDS == 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(MAX_BACKENDS).to_equal(4)
```

</details>

#### AC-3: 5th log_register_backend after 4 successful returns error sentinel

1. log remove backend
2. log remove backend
3. log remove backend
4. log remove backend


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s1 = ring_backend_new(8)
val s2 = ring_backend_new(8)
val s3 = ring_backend_new(8)
val s4 = ring_backend_new(8)
val s5 = ring_backend_new(8)
val id1 = log_register_backend(s1.ops)
val id2 = log_register_backend(s2.ops)
val id3 = log_register_backend(s3.ops)
val id4 = log_register_backend(s4.ops)
expect(id1).to_be_greater_than(-1)
expect(id2).to_be_greater_than(-1)
expect(id3).to_be_greater_than(-1)
expect(id4).to_be_greater_than(-1)
# 5th must fail. Phase 5 returns -1 (or NoSlot variant) as the sentinel.
val id5 = log_register_backend(s5.ops)
expect(id5).to_equal(-1)
log_remove_backend(id1)
log_remove_backend(id2)
log_remove_backend(id3)
log_remove_backend(id4)
```

</details>

### log facade — backend removal (AC-3)

#### AC-3: log_remove_backend(id) stops delivery to that slot

1. log set level
2. ring backend clear
3. ring backend clear
4. log info
   - Expected: ring_backend_count(sink_a) equals `1`
   - Expected: ring_backend_count(sink_b) equals `1`
5. log remove backend
6. log info
   - Expected: ring_backend_count(sink_a) equals `1`
   - Expected: ring_backend_count(sink_b) equals `2`
7. log remove backend


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
log_set_level(LOG_INFO)
val sink_a = ring_backend_new(64)
val sink_b = ring_backend_new(64)
val id_a = log_register_backend(sink_a.ops)
val id_b = log_register_backend(sink_b.ops)
ring_backend_clear(sink_a)
ring_backend_clear(sink_b)
log_info(SUBSYS_KERN, "both")
expect(ring_backend_count(sink_a)).to_equal(1)
expect(ring_backend_count(sink_b)).to_equal(1)
log_remove_backend(id_a)
log_info(SUBSYS_KERN, "only-b")
# A frozen at 1, B advances to 2.
expect(ring_backend_count(sink_a)).to_equal(1)
expect(ring_backend_count(sink_b)).to_equal(2)
log_remove_backend(id_b)
```

</details>

#### AC-3: removed slot is reusable

1. log remove backend
2. log remove backend


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s1 = ring_backend_new(8)
val id1 = log_register_backend(s1.ops)
log_remove_backend(id1)
# Same slot must accept a new registration.
val s2 = ring_backend_new(8)
val id2 = log_register_backend(s2.ops)
expect(id2).to_be_greater_than(-1)
log_remove_backend(id2)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
