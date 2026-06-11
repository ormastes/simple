# skybox_spec

> Engine Skybox — cubemap, reflection probe, and skybox manager tests

<!-- sdn-diagram:id=skybox_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=skybox_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

skybox_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=skybox_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# skybox_spec

Engine Skybox — cubemap, reflection probe, and skybox manager tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/skybox_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Engine Skybox — cubemap, reflection probe, and skybox manager tests

Tests cubemap face management, completeness checks, reflection probe
creation, skybox manager assignment, gradient sky, and clear behavior.

## Scenarios

### Cubemap

#### starts empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cm = Cubemap.new("test_sky")
expect(cm.name).to_equal("test_sky")
expect(cm.face_count()).to_equal(0)
expect(cm.is_complete()).to_equal(false)
```

</details>

#### set_face adds a face

1. var cm = Cubemap new
2. cm set face
   - Expected: cm.face_count() equals `1`
   - Expected: cm.get_face("px") equals `tex/px.png`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cm = Cubemap.new("sky")
cm.set_face("px", "tex/px.png")
expect(cm.face_count()).to_equal(1)
expect(cm.get_face("px")).to_equal("tex/px.png")
```

</details>

#### set_face updates existing face

1. var cm = Cubemap new
2. cm set face
3. cm set face
   - Expected: cm.face_count() equals `1`
   - Expected: cm.get_face("px") equals `new.png`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cm = Cubemap.new("sky")
cm.set_face("px", "old.png")
cm.set_face("px", "new.png")
expect(cm.face_count()).to_equal(1)
expect(cm.get_face("px")).to_equal("new.png")
```

</details>

#### get_face returns empty for missing face

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cm = Cubemap.new("sky")
expect(cm.get_face("px")).to_equal("")
```

</details>

#### is_complete returns true with all 6 faces

1. var cm = Cubemap new
2. cm set face
3. cm set face
4. cm set face
5. cm set face
6. cm set face
   - Expected: cm.is_complete() is false
7. cm set face
   - Expected: cm.is_complete() is true
   - Expected: cm.face_count() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cm = Cubemap.new("sky")
cm.set_face("px", "a.png")
cm.set_face("nx", "b.png")
cm.set_face("py", "c.png")
cm.set_face("ny", "d.png")
cm.set_face("pz", "e.png")
expect(cm.is_complete()).to_equal(false)
cm.set_face("nz", "f.png")
expect(cm.is_complete()).to_equal(true)
expect(cm.face_count()).to_equal(6)
```

</details>

### ReflectionProbe

#### creates with correct fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = ReflectionProbe.new("probe1", 1.0, 2.0, 3.0, 10.0, 256)
expect(probe.name).to_equal("probe1")
expect(probe.position_x).to_equal(1.0)
expect(probe.position_y).to_equal(2.0)
expect(probe.position_z).to_equal(3.0)
expect(probe.radius).to_equal(10.0)
expect(probe.resolution).to_equal(256)
```

</details>

### SkyboxManager

#### starts with no skybox

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = SkyboxManager.new()
expect(mgr.has_skybox()).to_equal(false)
expect(mgr.probe_count()).to_equal(0)
```

</details>

#### set_skybox enables skybox

1. var mgr = SkyboxManager new
2. var cm = Cubemap new
3. cm set face
4. mgr set skybox
   - Expected: mgr.has_skybox() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = SkyboxManager.new()
var cm = Cubemap.new("sky")
cm.set_face("px", "a.png")
mgr.set_skybox(cm)
expect(mgr.has_skybox()).to_equal(true)
```

</details>

#### set_gradient updates colors

1. var mgr = SkyboxManager new
2. mgr set gradient
   - Expected: mgr.sky_color_top_r equals `0.2`
   - Expected: mgr.sky_color_top_g equals `0.4`
   - Expected: mgr.sky_color_top_b equals `0.8`
   - Expected: mgr.sky_color_bottom_r equals `0.1`
   - Expected: mgr.sky_color_bottom_g equals `0.1`
   - Expected: mgr.sky_color_bottom_b equals `0.1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = SkyboxManager.new()
mgr.set_gradient(0.2, 0.4, 0.8, 0.1, 0.1, 0.1)
expect(mgr.sky_color_top_r).to_equal(0.2)
expect(mgr.sky_color_top_g).to_equal(0.4)
expect(mgr.sky_color_top_b).to_equal(0.8)
expect(mgr.sky_color_bottom_r).to_equal(0.1)
expect(mgr.sky_color_bottom_g).to_equal(0.1)
expect(mgr.sky_color_bottom_b).to_equal(0.1)
```

</details>

#### add_probe returns index

1. var mgr = SkyboxManager new
   - Expected: idx0 equals `0`
   - Expected: idx1 equals `1`
   - Expected: mgr.probe_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = SkyboxManager.new()
val p0 = ReflectionProbe.new("p0", 0.0, 0.0, 0.0, 5.0, 128)
val p1 = ReflectionProbe.new("p1", 1.0, 1.0, 1.0, 10.0, 256)
val idx0 = mgr.add_probe(p0)
val idx1 = mgr.add_probe(p1)
expect(idx0).to_equal(0)
expect(idx1).to_equal(1)
expect(mgr.probe_count()).to_equal(2)
```

</details>

#### clear resets everything

1. var mgr = SkyboxManager new
2. var cm = Cubemap new
3. cm set face
4. mgr set skybox
5. mgr set gradient
6. mgr add probe
7. mgr clear
   - Expected: mgr.has_skybox() is false
   - Expected: mgr.probe_count() equals `0`
   - Expected: mgr.sky_color_top_r equals `0.0`
   - Expected: mgr.sky_color_bottom_r equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = SkyboxManager.new()
var cm = Cubemap.new("sky")
cm.set_face("px", "a.png")
mgr.set_skybox(cm)
mgr.set_gradient(1.0, 1.0, 1.0, 0.5, 0.5, 0.5)
val probe = ReflectionProbe.new("p", 0.0, 0.0, 0.0, 5.0, 128)
mgr.add_probe(probe)
mgr.clear()
expect(mgr.has_skybox()).to_equal(false)
expect(mgr.probe_count()).to_equal(0)
expect(mgr.sky_color_top_r).to_equal(0.0)
expect(mgr.sky_color_bottom_r).to_equal(0.0)
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


</details>
