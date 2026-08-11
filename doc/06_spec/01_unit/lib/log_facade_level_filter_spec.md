# log_facade_level_filter_spec

> log-lib-drivers Phase 4 spec — facade level filtering & per-subsys filter.

<!-- sdn-diagram:id=log_facade_level_filter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=log_facade_level_filter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

log_facade_level_filter_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=log_facade_level_filter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# log_facade_level_filter_spec

log-lib-drivers Phase 4 spec — facade level filtering & per-subsys filter.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/log_facade_level_filter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

log-lib-drivers Phase 4 spec — facade level filtering & per-subsys filter.

Covers AC-3 (unified facade with swappable backend; level can be changed
at runtime per-subsystem) and AC-6a (facade level filter).

Status: RED PHASE. Phase 5 has not implemented `std.log.facade` yet.
These tests will fail to import / fail to resolve names until Phase 5
lands the noalloc facade described in `.sstack/log-lib-drivers/state.md`
section 3-arch §B-D-H.

Phase 3 contract (locked):
  - Levels: TRACE=0, DEBUG=1, INFO=2, WARN=3, ERROR=4, FATAL=5, OFF=6
  - Per-subsys filter: subsys IDs are integer constants (SUBSYS_*),
    g_subsys_level[id] = 0xFF means "fall through to global"
  - EnvFilter syntax: "net=debug,vfs=warn,*=info" — `*` sets global
  - effective_level(subsys) returns per-subsys override OR global

## Scenarios

### log facade — level enum sanity (AC-6a)

#### AC-6a: level enum numeric values are TRACE..OFF = 0..6

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(LOG_TRACE).to_equal(0)
expect(LOG_DEBUG).to_equal(1)
expect(LOG_INFO).to_equal(2)
expect(LOG_WARN).to_equal(3)
expect(LOG_ERROR).to_equal(4)
expect(LOG_FATAL).to_equal(5)
expect(LOG_OFF).to_equal(6)
```

</details>

#### AC-6a: lower numeric value = more verbose (TRACE most, OFF silent)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(LOG_TRACE).to_be_less_than(LOG_DEBUG)
expect(LOG_DEBUG).to_be_less_than(LOG_INFO)
expect(LOG_INFO).to_be_less_than(LOG_WARN)
expect(LOG_WARN).to_be_less_than(LOG_ERROR)
expect(LOG_ERROR).to_be_less_than(LOG_FATAL)
expect(LOG_FATAL).to_be_less_than(LOG_OFF)
```

</details>

### log facade — global level filter (AC-3, AC-6a)

#### AC-3: log_set_level(WARN) drops INFO emissions

- log set level
- ring backend clear
- log info
   - Expected: ring_backend_count(sink) equals `0`
- log remove backend


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Arrange: register a sink we can inspect.
val sink = ring_backend_new(64)
val id = log_register_backend(sink.ops)
log_set_level(LOG_WARN)
ring_backend_clear(sink)
# Act
log_info(SUBSYS_KERN, "should be filtered")
# Assert
expect(ring_backend_count(sink)).to_equal(0)
log_remove_backend(id)
```

</details>

#### AC-3: log_set_level(WARN) admits WARN+ emissions

- log set level
- ring backend clear
- log warn
- log error
- log fatal
   - Expected: ring_backend_count(sink) equals `3`
- log remove backend


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sink = ring_backend_new(64)
val id = log_register_backend(sink.ops)
log_set_level(LOG_WARN)
ring_backend_clear(sink)
log_warn(SUBSYS_KERN, "warn should pass")
log_error(SUBSYS_KERN, "error should pass")
log_fatal(SUBSYS_KERN, "fatal should pass")
expect(ring_backend_count(sink)).to_equal(3)
log_remove_backend(id)
```

</details>

### log facade — per-subsystem level filter (AC-3, AC-6a)

#### AC-3: log_set_subsys_level(NET, DEBUG) admits NET DEBUG when global=WARN

- log set level
- log set subsys level
- ring backend clear
- log debug
- log debug
   - Expected: ring_backend_count(sink) equals `1`
   - Expected: ring_backend_subsys_at(sink, 0) equals `SUBSYS_NET`
   - Expected: ring_backend_subsys_at(sink, 1) equals `-1`
- log remove backend


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sink = ring_backend_new(64)
val id = log_register_backend(sink.ops)
log_set_level(LOG_WARN)
log_set_subsys_level(SUBSYS_NET, LOG_DEBUG)
ring_backend_clear(sink)
# Act
log_debug(SUBSYS_NET, "net debug — should emit (override admits)")
log_debug(SUBSYS_VFS, "vfs debug — should be filtered (falls through to WARN)")
# Assert
expect(ring_backend_count(sink)).to_equal(1)
expect(ring_backend_subsys_at(sink, 0)).to_equal(SUBSYS_NET)
expect(ring_backend_subsys_at(sink, 1)).to_equal(-1)
log_remove_backend(id)
```

</details>

#### AC-3: per-subsys override only affects that subsys; others fall through

- log set level
- log set subsys level
- ring backend clear
- log info
- log info
   - Expected: ring_backend_count(sink) equals `1`
   - Expected: ring_backend_subsys_at(sink, 0) equals `SUBSYS_NET`
- log remove backend


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sink = ring_backend_new(64)
val id = log_register_backend(sink.ops)
log_set_level(LOG_INFO)
log_set_subsys_level(SUBSYS_VFS, LOG_WARN)
ring_backend_clear(sink)
log_info(SUBSYS_VFS, "vfs info — filtered by override")
log_info(SUBSYS_NET, "net info — admitted by global INFO")
expect(ring_backend_count(sink)).to_equal(1)
expect(ring_backend_subsys_at(sink, 0)).to_equal(SUBSYS_NET)
log_remove_backend(id)
```

</details>

### log facade — EnvFilter parser (AC-3)

#### AC-3: log_init_from_config('net=debug,vfs=warn,*=info') sets per-subsys + global

- log init from config
   - Expected: effective_level(SUBSYS_NET) equals `LOG_DEBUG`
   - Expected: effective_level(SUBSYS_VFS) equals `LOG_WARN`
   - Expected: effective_level(SUBSYS_KERN) equals `LOG_INFO)   # falls through to global`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The parser is locked in Phase 3 §D.
log_init_from_config("net=debug,vfs=warn,*=info")
expect(effective_level(SUBSYS_NET)).to_equal(LOG_DEBUG)
expect(effective_level(SUBSYS_VFS)).to_equal(LOG_WARN)
expect(effective_level(SUBSYS_KERN)).to_equal(LOG_INFO)   # falls through to global
```

</details>

#### AC-3: log_init_from_config('') leaves defaults (global=INFO)

- log init from config
   - Expected: effective_level(SUBSYS_KERN) equals `LOG_INFO`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
log_init_from_config("")
expect(effective_level(SUBSYS_KERN)).to_equal(LOG_INFO)
```

</details>

#### AC-3: unknown subsys names are skipped (do not crash)

- log init from config
   - Expected: effective_level(SUBSYS_KERN) equals `LOG_WARN`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Phase 3 §D: unknown name → 1 warn line, parser keeps going.
log_init_from_config("doesnotexist=debug,*=warn")
expect(effective_level(SUBSYS_KERN)).to_equal(LOG_WARN)
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
