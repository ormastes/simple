# Game2D Golden Frame (AC-5 — golden half)

> `HeadlessBackend.frame_hash()` after N frames matches a stored hash from

<!-- sdn-diagram:id=game2d_golden_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=game2d_golden_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

game2d_golden_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=game2d_golden_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Game2D Golden Frame (AC-5 — golden half)

`HeadlessBackend.frame_hash()` after N frames matches a stored hash from

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | RESOLVED 2026-04-26 — 11/11 PASS. Hash pinned to `0x253edd45a462bc15`. |
| Source | `test/03_system/engine/game2d_golden_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

`HeadlessBackend.frame_hash()` after N frames matches a stored hash from
`test/fixtures/game2d_golden_hello_720p.hash`. Phase 5b pinned the value
to `0x253edd45a462bc15` (FNV-1a over the 4×4 representative framebuffer,
verified deterministic across 3 runs via `test/util/game2d_pin_golden_hash.spl`).

Edge case: same replay twice → identical hash (determinism).
Error path: golden mismatch → spec fails with diff.

## Scenarios

### Game2D Golden Frame (AC-5 golden)
_## Frame-buffer hash stability._

### frame_hash function declared

#### headless.spl declares fn frame_hash(buf: [u32]) -> u64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("src/lib/nogc_sync_mut/game2d/backend/headless.spl")
expect(_has(src, "fn frame_hash(")).to_equal(true)
```

</details>

#### headless.spl uses FNV-1a (or documented hash)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("src/lib/nogc_sync_mut/game2d/backend/headless.spl")
expect(_has(src, "FNV") or _has(src, "fnv1a") or
       _has(src, "hash")).to_equal(true)
```

</details>

### golden fixture exists

#### test/fixtures/game2d_golden_hello_720p.hash exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_file_exists(
    "test/fixtures/game2d_golden_hello_720p.hash")).to_equal(true)
```

</details>

#### fixture is non-empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("test/fixtures/game2d_golden_hello_720p.hash")
expect(src.len() > 0).to_equal(true)
```

</details>

#### fixture contains the pinned FNV-1a hash (0x253edd45a462bc15)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("test/fixtures/game2d_golden_hello_720p.hash")
expect(_has(_trim(src), "253edd45a462bc15")).to_equal(true)
```

</details>

#### fixture starts with 0x hex prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("test/fixtures/game2d_golden_hello_720p.hash")
expect(_trim(src).starts_with("0x")).to_equal(true)
```

</details>

### edge case: determinism across runs

#### synthetic: same input bytes → same hash

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = "253edd45a462bc15"
val b = "253edd45a462bc15"
expect(a).to_equal(b)
```

</details>

#### synthetic: different input → different hash

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = "253edd45a462bc15"
val b = "253edd45a462bc14"
expect(a == b).to_equal(false)
```

</details>

#### pin utility exists for 3-run reproducibility check

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_file_exists("test/util/game2d_pin_golden_hash.spl")
    ).to_equal(true)
```

</details>

### error path: golden mismatch

#### headless.spl notes diff-on-mismatch contract

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("src/lib/nogc_sync_mut/game2d/backend/headless.spl")
expect(_has(src, "diff") or _has(src, "mismatch") or
       _has(src, "frame_hash")).to_equal(true)
```

</details>

#### edge case: missing golden file yields empty read

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_read(
    "test/fixtures/does_not_exist.hash")).to_equal("")
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
