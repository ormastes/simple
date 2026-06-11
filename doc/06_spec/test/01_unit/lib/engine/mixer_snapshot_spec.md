# mixer_snapshot_spec

> Mixer Snapshot — snapshot-based audio mixing tests

<!-- sdn-diagram:id=mixer_snapshot_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mixer_snapshot_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mixer_snapshot_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mixer_snapshot_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# mixer_snapshot_spec

Mixer Snapshot — snapshot-based audio mixing tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/mixer_snapshot_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Mixer Snapshot — snapshot-based audio mixing tests

Tests MixerSnapshot volume management, MixerSnapshotManager registration,
apply, lerp transitions, and volume interpolation.

## Scenarios

### MixerSnapshot

#### creates empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snap = MixerSnapshot.new("combat")
expect(snap.name).to_equal("combat")
expect(snap.group_count()).to_equal(0)
```

</details>

#### set_volume adds group

1. var snap = MixerSnapshot new
2. snap set volume
   - Expected: snap.group_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var snap = MixerSnapshot.new("combat")
snap.set_volume("sfx", 0.8)
expect(snap.group_count()).to_equal(1)
val vol = snap.get_volume("sfx")
val vol_i = vol * 1000.0
expect(vol_i).to_be_greater_than(799.0)
expect(vol_i).to_be_less_than(801.0)
```

</details>

#### set_volume updates existing group

1. var snap = MixerSnapshot new
2. snap set volume
3. snap set volume
   - Expected: snap.group_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var snap = MixerSnapshot.new("combat")
snap.set_volume("sfx", 0.8)
snap.set_volume("sfx", 0.5)
expect(snap.group_count()).to_equal(1)
val vol = snap.get_volume("sfx")
val vol_i = vol * 1000.0
expect(vol_i).to_be_greater_than(499.0)
expect(vol_i).to_be_less_than(501.0)
```

</details>

#### get_volume returns 1.0 for unknown group

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snap = MixerSnapshot.new("test")
val vol = snap.get_volume("nonexistent")
val vol_i = vol * 1000.0
expect(vol_i).to_be_greater_than(999.0)
expect(vol_i).to_be_less_than(1001.0)
```

</details>

### MixerSnapshotManager

#### starts empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = MixerSnapshotManager.new()
expect(mgr.snapshot_count()).to_equal(0)
expect(mgr.is_transitioning()).to_equal(false)
```

</details>

#### register_snapshot increases count

1. var mgr = MixerSnapshotManager new
2. var snap = MixerSnapshot new
3. snap set volume
4. mgr register snapshot
   - Expected: mgr.snapshot_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = MixerSnapshotManager.new()
var snap = MixerSnapshot.new("calm")
snap.set_volume("music", 0.9)
mgr.register_snapshot(snap)
expect(mgr.snapshot_count()).to_equal(1)
```

</details>

#### apply_snapshot sets current volumes

1. var mgr = MixerSnapshotManager new
2. var snap = MixerSnapshot new
3. snap set volume
4. snap set volume
5. mgr register snapshot
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = MixerSnapshotManager.new()
var snap = MixerSnapshot.new("combat")
snap.set_volume("sfx", 0.8)
snap.set_volume("music", 0.3)
mgr.register_snapshot(snap)
val ok = mgr.apply_snapshot("combat")
expect(ok).to_equal(true)
val sfx_vol = mgr.get_current_volume("sfx")
val sfx_i = sfx_vol * 1000.0
expect(sfx_i).to_be_greater_than(799.0)
expect(sfx_i).to_be_less_than(801.0)
```

</details>

#### apply_snapshot returns false for unknown

1. var mgr = MixerSnapshotManager new
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = MixerSnapshotManager.new()
val ok = mgr.apply_snapshot("nope")
expect(ok).to_equal(false)
```

</details>

#### transition_to starts interpolation

1. var mgr = MixerSnapshotManager new
2. var calm = MixerSnapshot new
3. calm set volume
4. calm set volume
5. var combat = MixerSnapshot new
6. combat set volume
7. combat set volume
8. mgr register snapshot
9. mgr register snapshot
10. mgr apply snapshot
   - Expected: ok is true
   - Expected: mgr.is_transitioning() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = MixerSnapshotManager.new()
var calm = MixerSnapshot.new("calm")
calm.set_volume("sfx", 0.5)
calm.set_volume("music", 0.9)
var combat = MixerSnapshot.new("combat")
combat.set_volume("sfx", 1.0)
combat.set_volume("music", 0.3)
mgr.register_snapshot(calm)
mgr.register_snapshot(combat)
mgr.apply_snapshot("calm")
val ok = mgr.transition_to("combat", 1.0)
expect(ok).to_equal(true)
expect(mgr.is_transitioning()).to_equal(true)
```

</details>

#### update lerps volumes during transition

1. var mgr = MixerSnapshotManager new
2. var calm = MixerSnapshot new
3. calm set volume
4. var loud = MixerSnapshot new
5. loud set volume
6. mgr register snapshot
7. mgr register snapshot
8. mgr apply snapshot
9. mgr transition to
10. mgr update


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = MixerSnapshotManager.new()
var calm = MixerSnapshot.new("calm")
calm.set_volume("sfx", 0.0)
var loud = MixerSnapshot.new("loud")
loud.set_volume("sfx", 1.0)
mgr.register_snapshot(calm)
mgr.register_snapshot(loud)
mgr.apply_snapshot("calm")
mgr.transition_to("loud", 1.0)
# At t=0.5, sfx should be lerp(0.0, 1.0, 0.5) = 0.5
mgr.update(0.5)
val vol = mgr.get_current_volume("sfx")
val vol_i = vol * 1000.0
expect(vol_i).to_be_greater_than(490.0)
expect(vol_i).to_be_less_than(510.0)
```

</details>

#### transition completes after full duration

1. var mgr = MixerSnapshotManager new
2. var a = MixerSnapshot new
3. a set volume
4. var b = MixerSnapshot new
5. b set volume
6. mgr register snapshot
7. mgr register snapshot
8. mgr apply snapshot
9. mgr transition to
10. mgr update
   - Expected: mgr.is_transitioning() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = MixerSnapshotManager.new()
var a = MixerSnapshot.new("a")
a.set_volume("music", 0.2)
var b = MixerSnapshot.new("b")
b.set_volume("music", 0.8)
mgr.register_snapshot(a)
mgr.register_snapshot(b)
mgr.apply_snapshot("a")
mgr.transition_to("b", 0.5)
mgr.update(0.6)
expect(mgr.is_transitioning()).to_equal(false)
val vol = mgr.get_current_volume("music")
val vol_i = vol * 1000.0
expect(vol_i).to_be_greater_than(799.0)
expect(vol_i).to_be_less_than(801.0)
```

</details>

#### get_current_volume returns 1.0 for unknown group

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = MixerSnapshotManager.new()
val vol = mgr.get_current_volume("unknown")
val vol_i = vol * 1000.0
expect(vol_i).to_be_greater_than(999.0)
expect(vol_i).to_be_less_than(1001.0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
