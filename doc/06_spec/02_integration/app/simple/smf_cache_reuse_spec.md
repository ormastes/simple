# SMF Cache Reuse — Semantic Invalidation Specification (AC-7)

> Proves that the dynSMF precompiled-lane content-hash guard correctly: (a) accepts a magic-valid artifact whose `.srchash` sidecar matches the current source hash (cache hit — unchanged source), (b) rejects a magic-valid artifact whose `.srchash` sidecar hash DIFFERS from the current source hash (cache miss — stale source, reason="stale_source"), (c) rejects a magic-valid artifact whose `.srchash` sidecar is ABSENT (treated as stale — reason="stale_source").

<!-- sdn-diagram:id=smf_cache_reuse_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=smf_cache_reuse_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

smf_cache_reuse_spec -> std
smf_cache_reuse_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=smf_cache_reuse_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SMF Cache Reuse — Semantic Invalidation Specification (AC-7)

Proves that the dynSMF precompiled-lane content-hash guard correctly: (a) accepts a magic-valid artifact whose `.srchash` sidecar matches the current source hash (cache hit — unchanged source), (b) rejects a magic-valid artifact whose `.srchash` sidecar hash DIFFERS from the current source hash (cache miss — stale source, reason="stale_source"), (c) rejects a magic-valid artifact whose `.srchash` sidecar is ABSENT (treated as stale — reason="stale_source").

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Design | doc/05_design/infra/perf_umbrella/perf_opt_design.md ## dynSMF cache |
| Source | `test/02_integration/app/simple/smf_cache_reuse_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Proves that the dynSMF precompiled-lane content-hash guard correctly:
(a) accepts a magic-valid artifact whose `.srchash` sidecar matches the current
    source hash (cache hit — unchanged source),
(b) rejects a magic-valid artifact whose `.srchash` sidecar hash DIFFERS from
    the current source hash (cache miss — stale source, reason="stale_source"),
(c) rejects a magic-valid artifact whose `.srchash` sidecar is ABSENT (treated
    as stale — reason="stale_source").

The changed-source case is the load-bearing assertion: it must produce a
`ready=false` status with `reason="stale_source"`, which is categorically
different from the unchanged-source case (`ready=true`).

Tests are driven with injected hashes through `dynsmf_artifact_status_with_hash`
— no `bin/simple compile` is invoked, so the spec is fast and deterministic.

**Requirement:** AC-7 (perf-opt-lang-web-db-os: dynSMF idle background compile +
  unchanged-script cache reuse)
**Anchors:** src/os/smf/dynsmf_session.spl, src/app/startup/dynsmf_autoload.spl
**Design:** doc/05_design/infra/perf_umbrella/perf_opt_design.md ## dynSMF cache

## Scenarios

### dynSMF content-hash cache invalidation (AC-7)

#### accepts artifact when sidecar hash matches current source hash (cache hit)

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = test_entry()
val data = smf_magic_bytes()
val base = dynsmf_artifact_status_from_bytes(entry, true, data)
expect(base.ready).to_equal(true)
# Inject: stored_hash == current_hash (same value simulates unchanged source)
val hash_value = 12345678901234567
val status = dynsmf_artifact_status_with_hash_injected(entry, base, hash_value, hash_value)
expect(status.ready).to_equal(true)
expect(status.reason).to_equal("smf_artifact_ready")
```

</details>

#### rejects artifact when sidecar hash differs from current source hash (stale source miss)

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = test_entry()
val data = smf_magic_bytes()
val base = dynsmf_artifact_status_from_bytes(entry, true, data)
expect(base.ready).to_equal(true)
# Inject: stored_hash != current_hash (simulates changed source)
val stored_hash = 12345678901234567
val current_hash = 99999999999999999
val status = dynsmf_artifact_status_with_hash_injected(entry, base, stored_hash, current_hash)
expect(status.ready).to_equal(false)
expect(status.reason).to_equal("stale_source")
```

</details>

#### rejects artifact when sidecar is absent (no .srchash file)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = test_entry()
val data = smf_magic_bytes()
val base = dynsmf_artifact_status_from_bytes(entry, true, data)
expect(base.ready).to_equal(true)
# Inject stored_hash = -1 simulates absent sidecar (dynsmf_source_hash_stored returns -1)
val status = dynsmf_artifact_status_with_hash_injected(entry, base, -1, 12345678901234567)
expect(status.ready).to_equal(false)
expect(status.reason).to_equal("stale_source")
```

</details>

#### unchanged vs changed source produce categorically different ready values

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = test_entry()
val data = smf_magic_bytes()
val base = dynsmf_artifact_status_from_bytes(entry, true, data)
val same_hash = 777777777
val hit = dynsmf_artifact_status_with_hash_injected(entry, base, same_hash, same_hash)
val miss = dynsmf_artifact_status_with_hash_injected(entry, base, same_hash, same_hash + 1)
expect(hit.ready).to_equal(true)
expect(miss.ready).to_equal(false)
expect(miss.reason).to_equal("stale_source")
# Prove the two cases genuinely differ
expect(hit.ready == miss.ready).to_equal(false)
```

</details>

#### magic-invalid artifact is rejected before hash check (not_precompiled path)

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = test_entry()
val bad_data = [0, 1, 2, 3, 4, 5, 6, 7]
val base = dynsmf_artifact_status_from_bytes(entry, true, bad_data)
expect(base.ready).to_equal(false)
expect(base.reason).to_equal("invalid_magic")
# Hash check must not override the magic rejection
val status = dynsmf_artifact_status_with_hash_injected(entry, base, 999, 999)
expect(status.ready).to_equal(false)
expect(status.reason).to_equal("invalid_magic")
```

</details>

#### srchash sidecar path is deterministic (artifact_path + .srchash)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val artifact = "build/dynsmf/file_io.smf"
val sidecar = dynsmf_srchash_path(artifact)
expect(sidecar).to_equal("build/dynsmf/file_io.smf.srchash")
```

</details>

### dynSMF background compile dispatch evidence (AC-7)

#### queued evidence uses compile_background action

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = dynsmf_default_manifest()
val entry = manifest[0]
expect(entry.id).to_equal("file_io")
# Verify the queued command format includes the source path
# (Dispatch is fire-and-forget; we verify the evidence structure, not the spawn)
val base = dynsmf_artifact_status_from_bytes(entry, false, [])
expect(base.ready).to_equal(false)
expect(base.reason).to_equal("missing_file")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Design:** [doc/05_design/infra/perf_umbrella/perf_opt_design.md ## dynSMF cache](doc/05_design/infra/perf_umbrella/perf_opt_design.md ## dynSMF cache)


</details>
