# watcher_daemon_spec

> Watcher Daemon Specification

<!-- sdn-diagram:id=watcher_daemon_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=watcher_daemon_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

watcher_daemon_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=watcher_daemon_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# watcher_daemon_spec

Watcher Daemon Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #WATCH-041 to #WATCH-050 |
| Category | Infrastructure |
| Status | Active |
| Source | `test/01_unit/compiler/watcher/watcher_daemon_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Watcher Daemon Specification

Tests the background watcher daemon's poll cycle and request processing.
Uses module-level functions for all state mutations (closure limitation).

## Scenarios

### WatcherDaemon

### lifecycle

#### starts in idle state

1. d reset
2. d start
   - Expected: d_get_running() is true
   - Expected: d_get_status() equals `D_IDLE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
d_reset()
d_start()
expect(d_get_running()).to_equal(true)
expect(d_get_status()).to_equal(D_IDLE)
```

</details>

#### shuts down cleanly

1. d reset
2. d start
3. d shutdown
   - Expected: d_get_running() is false
   - Expected: d_get_status() equals `D_SHUTTING`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
d_reset()
d_start()
d_shutdown()
expect(d_get_running()).to_equal(false)
expect(d_get_status()).to_equal(D_SHUTTING)
```

</details>

### poll cycle

#### processes file changes

1. d reset
2. d start
3. d poll
   - Expected: d_get_files_processed() equals `2`
   - Expected: d_get_shb_gen_len() equals `2`
   - Expected: d_get_cycle_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
d_reset()
d_start()
d_poll(["src/main.spl", "src/lib.spl"], [], [])
expect(d_get_files_processed()).to_equal(2)
expect(d_get_shb_gen_len()).to_equal(2)
expect(d_get_cycle_count()).to_equal(1)
```

</details>

#### processes requests

1. d reset
2. d start
3. d poll
   - Expected: d_get_files_processed() equals `2`
   - Expected: d_get_shb_gen_len() equals `1`
   - Expected: d_get_smf_gen_len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
d_reset()
d_start()
d_poll([], ["src/main.spl", "src/lib.spl"], ["shb", "smf"])
expect(d_get_files_processed()).to_equal(2)
expect(d_get_shb_gen_len()).to_equal(1)
expect(d_get_smf_gen_len()).to_equal(1)
```

</details>

#### handles both changes and requests

1. d reset
2. d start
3. d poll
   - Expected: d_get_files_processed() equals `2`
   - Expected: d_get_shb_gen_len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
d_reset()
d_start()
d_poll(["src/a.spl"], ["src/b.spl"], ["shb"])
expect(d_get_files_processed()).to_equal(2)
expect(d_get_shb_gen_len()).to_equal(2)
```

</details>

#### does nothing when not running

1. d reset
2. d poll
   - Expected: d_get_files_processed() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
d_reset()
d_poll(["src/main.spl"], [], [])
expect(d_get_files_processed()).to_equal(0)
```

</details>

### state tracking

#### increments cycle count

1. d reset
2. d start
3. d poll
4. d poll
5. d poll
   - Expected: d_get_cycle_count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
d_reset()
d_start()
d_poll([], [], [])
d_poll([], [], [])
d_poll([], [], [])
expect(d_get_cycle_count()).to_equal(3)
```

</details>

#### accumulates files processed

1. d reset
2. d start
3. d poll
4. d poll
   - Expected: d_get_files_processed() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
d_reset()
d_start()
d_poll(["a.spl"], [], [])
d_poll(["b.spl", "c.spl"], [], [])
expect(d_get_files_processed()).to_equal(3)
```

</details>

#### returns to idle after cycle

1. d reset
2. d start
3. d poll
   - Expected: d_get_status() equals `D_IDLE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
d_reset()
d_start()
d_poll(["a.spl"], [], [])
expect(d_get_status()).to_equal(D_IDLE)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
