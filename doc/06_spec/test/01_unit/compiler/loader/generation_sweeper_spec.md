# generation_sweeper_spec

> Generation Sweeper Specification

<!-- sdn-diagram:id=generation_sweeper_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=generation_sweeper_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

generation_sweeper_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=generation_sweeper_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# generation_sweeper_spec

Generation Sweeper Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #2011-2015 |
| Category | Infrastructure |
| Status | Active |
| Design | doc/05_design/resource_lifecycle_manager_design.md |
| Source | `test/01_unit/compiler/loader/generation_sweeper_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Generation Sweeper Specification

Tests epoch-based LRU eviction logic using mock implementations.
The actual compiler modules depend on FFI/loader internals not available
in interpreter mode, so we mock the core abstractions here.

## Scenarios

### GenerationSweeper

### epoch management

#### starts at epoch 0

1. sw reset
   - Expected: sw_get_epoch() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sw_reset()
expect(sw_get_epoch()).to_equal(0)
```

</details>

#### advances epoch

1. sw reset
   - Expected: e1 equals `1`
   - Expected: e2 equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sw_reset()
val e1 = sw_advance_epoch()
expect(e1).to_equal(1)
val e2 = sw_advance_epoch()
expect(e2).to_equal(2)
```

</details>

#### tracks marked symbols

1. sw reset
2. sw mark used
3. sw mark used
   - Expected: sw_tracked_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sw_reset()
sw_mark_used("fn_a")
sw_mark_used("fn_b")
expect(sw_tracked_count()).to_equal(2)
```

</details>

### stale detection

#### reports zero stale when all symbols are fresh

1. sw reset with age
2. sw mark used
3. sw advance epoch
   - Expected: sw_stale_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sw_reset_with_age(5)
sw_mark_used("fn_a")
sw_advance_epoch()
expect(sw_stale_count()).to_equal(0)
```

</details>

#### detects stale symbols after max_age epochs

1. sw reset with age
2. sw mark used
3. sw advance epoch
4. sw advance epoch
5. sw advance epoch
6. sw advance epoch
   - Expected: sw_stale_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sw_reset_with_age(3)
sw_mark_used("fn_old")
sw_advance_epoch()
sw_advance_epoch()
sw_advance_epoch()
sw_advance_epoch()
expect(sw_stale_count()).to_equal(1)
```

</details>

#### does not count recently used symbols as stale

1. sw reset with age
2. sw mark used
3. sw advance epoch
4. sw advance epoch
5. sw mark used
6. sw advance epoch
7. sw advance epoch
   - Expected: sw_stale_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sw_reset_with_age(3)
sw_mark_used("fn_fresh")
sw_advance_epoch()
sw_advance_epoch()
# Re-mark as used — resets last-used epoch
sw_mark_used("fn_fresh")
sw_advance_epoch()
sw_advance_epoch()
expect(sw_stale_count()).to_equal(0)
```

</details>

### stats

#### reports correct stats

1. sw reset with age
2. sw mark used
3. sw mark used
4. sw advance epoch
5. sw advance epoch
6. sw advance epoch
   - Expected: sw_get_epoch() equals `3`
   - Expected: sw_tracked_count() equals `2`
   - Expected: sw_stale_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sw_reset_with_age(2)
sw_mark_used("fn_a")
sw_mark_used("fn_b")
sw_advance_epoch()
sw_advance_epoch()
sw_advance_epoch()
expect(sw_get_epoch()).to_equal(3)
expect(sw_tracked_count()).to_equal(2)
expect(sw_stale_count()).to_equal(2)
```

</details>

### reset

#### clears all state on reset

1. sw reset
2. sw mark used
3. sw advance epoch
4. sw reset
   - Expected: sw_get_epoch() equals `0`
   - Expected: sw_tracked_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sw_reset()
sw_mark_used("fn_a")
sw_advance_epoch()
sw_reset()
expect(sw_get_epoch()).to_equal(0)
expect(sw_tracked_count()).to_equal(0)
```

</details>

### ResourceLifecycleManager sweep integration

### sweep delegation

#### delegates mark_used to sweeper

1. lm sweep reset
2. lm mark used
   - Expected: lm_get_sweep_tracked() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lm_sweep_reset()
lm_mark_used("test_fn")
expect(lm_get_sweep_tracked()).to_equal(1)
```

</details>

#### delegates advance_epoch to sweeper

1. lm sweep reset
   - Expected: e equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lm_sweep_reset()
val e = lm_advance_epoch()
expect(e).to_equal(1)
```

</details>

#### reports stats including sweep data

1. lm sweep reset
2. lm mark used
3. lm advance epoch
   - Expected: lm_get_sweep_epoch() equals `1`
   - Expected: lm_get_sweep_tracked() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lm_sweep_reset()
lm_mark_used("fn_x")
lm_advance_epoch()
expect(lm_get_sweep_epoch()).to_equal(1)
expect(lm_get_sweep_tracked()).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Design:** [doc/05_design/resource_lifecycle_manager_design.md](doc/05_design/resource_lifecycle_manager_design.md)


</details>
