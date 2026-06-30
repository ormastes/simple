# log_facade_back_compat_spec

> log-lib-drivers Phase 4 spec — back-compat for existing log call sites.

<!-- sdn-diagram:id=log_facade_back_compat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=log_facade_back_compat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

log_facade_back_compat_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=log_facade_back_compat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# log_facade_back_compat_spec

log-lib-drivers Phase 4 spec — back-compat for existing log call sites.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/log_facade_back_compat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

log-lib-drivers Phase 4 spec — back-compat for existing log call sites.

Covers AC-4 (back-compat: existing `log.info(...)` / `log.warn(...)`
call sites must keep working).

Status: RED PHASE. Phase 5 has not rerouted `nogc_sync_mut/log.spl`
through the new facade yet.

Phase 3 contract (locked, §F):
  - `use std.log.{error, warn, info, debug, fatal}` resolves; signatures
    `info(scope: text, msg: text)` etc. unchanged.
  - `nogc_sync_mut.log.spl` `_emit` rewritten to call
    `log_dispatch_text(canonical_level, subsys_from_scope(scope), bytes)`.
  - `subsys_from_scope("pkg")` -> SUBSYS_PKG, "cli" -> SUBSYS_CLI,
    "test" -> SUBSYS_TEST. Unknown scope -> SUBSYS_USER_BASE.
  - The duplicate `src/lib/nogc_sync_mut/src/log.spl` keeps working
    (marked DEPRECATED — Phase 6 deletes; this spec must NOT block on
    that decision).

## Scenarios

### log facade — top-level imports resolve (AC-4)

#### AC-4: `use std.log.{error, warn, info, debug}` resolves

1. log set level
2. ring backend clear
3. info
4. warn
5. debug
6. error
   - Expected: ring_backend_count(sink) equals `4`
7. log remove backend


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Compile-time check: if these names don't resolve, the file
# doesn't compile — which is the failure signal in red phase.
log_set_level(LOG_TRACE)
val sink = ring_backend_new(64)
val id = log_register_backend(sink.ops)
ring_backend_clear(sink)
info("pkg", "import smoke info")
warn("cli", "import smoke warn")
debug("test", "import smoke debug")
error("pkg", "import smoke error")
expect(ring_backend_count(sink)).to_equal(4)
log_remove_backend(id)
```

</details>

#### AC-4: log.info(scope, msg) emits without crashing

1. log set level
2. ring backend clear
3. info
4. warn
5. debug
6. error
7. log remove backend


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
log_set_level(LOG_TRACE)
val sink = ring_backend_new(64)
val id = log_register_backend(sink.ops)
ring_backend_clear(sink)
info("pkg", "package install starting")
warn("cli", "cli got a deprecation hit")
debug("test", "test runner spawned")
error("pkg", "package install failed")
expect(ring_backend_count(sink)).to_be_greater_than(3)
log_remove_backend(id)
```

</details>

### log facade — scope→subsys mapping (AC-4)

#### AC-4: subsys_from_scope routes legacy scopes to canonical IDs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(subsys_from_scope("pkg")).to_equal(SUBSYS_PKG)
expect(subsys_from_scope("cli")).to_equal(SUBSYS_CLI)
expect(subsys_from_scope("test")).to_equal(SUBSYS_TEST)
```

</details>

#### AC-4: unknown scope falls through to SUBSYS_USER_BASE

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(subsys_from_scope("not-a-known-scope")).to_equal(SUBSYS_USER_BASE)
```

</details>

### log facade — legacy emission round-trips through facade (AC-4)

#### AC-4: legacy info('pkg', ...) lands as SUBSYS_PKG record

1. log set level
2. ring backend clear
3. info
   - Expected: ring_backend_count(sink) equals `1`
   - Expected: ring_backend_subsys_at(sink, 0) equals `SUBSYS_PKG`
4. log remove backend


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
log_set_level(LOG_TRACE)
val sink = ring_backend_new(64)
val id = log_register_backend(sink.ops)
ring_backend_clear(sink)
info("pkg", "hello")
expect(ring_backend_count(sink)).to_equal(1)
expect(ring_backend_subsys_at(sink, 0)).to_equal(SUBSYS_PKG)
log_remove_backend(id)
```

</details>

#### AC-4: legacy warn('cli', ...) lands as SUBSYS_CLI record

1. log set level
2. ring backend clear
3. warn
   - Expected: ring_backend_subsys_at(sink, 0) equals `SUBSYS_CLI`
4. log remove backend


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
log_set_level(LOG_TRACE)
val sink = ring_backend_new(64)
val id = log_register_backend(sink.ops)
ring_backend_clear(sink)
warn("cli", "hi from cli")
expect(ring_backend_subsys_at(sink, 0)).to_equal(SUBSYS_CLI)
log_remove_backend(id)
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
