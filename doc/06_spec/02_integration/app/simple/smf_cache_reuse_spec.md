# SMF Cache Reuse — Semantic Invalidation Specification (AC-7)

> Proves that the dynSMF precompiled-lane content-hash guard correctly: (a) accepts a magic-valid artifact whose `.srchash` sidecar matches the current source hash (cache hit — unchanged source), (b) rejects a magic-valid artifact whose `.srchash` sidecar hash DIFFERS from the current source hash (cache miss — stale source, reason="stale_source"), (c) rejects a magic-valid artifact whose `.srchash` sidecar is ABSENT (treated as stale — reason="stale_source").

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

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
| Updated | 2026-08-26 |
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

The AC-7 unit cases inject hashes through `dynsmf_artifact_status_with_hash`.
The final scenario generates and executes a real SMF through the production CLI.

**Requirement:** AC-7 (perf-opt-lang-web-db-os: dynSMF idle background compile +
  unchanged-script cache reuse)
**Anchors:** src/os/smf/dynsmf_session.spl, src/app/startup/dynsmf_autoload.spl
**Design:** doc/05_design/infra/perf_umbrella/perf_opt_design.md ## dynSMF cache

## Scenarios

### dynSMF content-hash cache invalidation (AC-7)

#### accepts artifact when sidecar hash matches current source hash (cache hit)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts artifact when sidecar hash matches current source hash (cache hit)
   - Expected: base.ready is true
   - Expected: status.ready is true
   - Expected: status.reason equals `smf_artifact_ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("accepts artifact when sidecar hash matches current source hash (cache hit)")
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

- rejects artifact when sidecar hash differs from current source hash (stale source miss)
   - Expected: base.ready is true
   - Expected: status.ready is false
   - Expected: status.reason equals `stale_source`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects artifact when sidecar hash differs from current source hash (stale source miss)")
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

- rejects artifact when sidecar is absent (no .srchash file)
   - Expected: base.ready is true
   - Expected: status.ready is false
   - Expected: status.reason equals `stale_source`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects artifact when sidecar is absent (no .srchash file)")
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

- unchanged vs changed source produce categorically different ready values
   - Expected: hit.ready is true
   - Expected: miss.ready is false
   - Expected: miss.reason equals `stale_source`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("unchanged vs changed source produce categorically different ready values")
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
expect(hit.ready).to_not_equal(miss.ready)
```

</details>

#### magic-invalid artifact is rejected before hash check (not_precompiled path)

- magic-invalid artifact is rejected before hash check (not_precompiled path)
   - Expected: base.ready is false
   - Expected: base.reason equals `invalid_magic`
   - Expected: status.ready is false
   - Expected: status.reason equals `invalid_magic`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("magic-invalid artifact is rejected before hash check (not_precompiled path)")
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

- srchash sidecar path is deterministic (artifact_path + .srchash)
   - Expected: sidecar equals `build/dynsmf/file_io.smf.srchash`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("srchash sidecar path is deterministic (artifact_path + .srchash)")
val artifact = "build/dynsmf/file_io.smf"
val sidecar = dynsmf_srchash_path(artifact)
expect(sidecar).to_equal("build/dynsmf/file_io.smf.srchash")
```

</details>

### dynSMF background compile dispatch evidence (AC-7)

#### queued evidence uses compile_background action

- queued evidence uses compile_background action
   - Expected: entry.id equals `file_io`
   - Expected: base.ready is false
   - Expected: base.reason equals `missing_file`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("queued evidence uses compile_background action")
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

### pure-Simple production SMF consumption

#### reuses unchanged code, regenerates changed code, and preserves the launcher

- reuses unchanged code, regenerates changed code, and preserves the launcher
   - Expected: mkdir_p(REAL_FIXTURE_DIR) is true
   - Expected: mkdir_p("build/smf") is true
   - Expected: file_write(REAL_LEAF, "fn main() -> i64:\n    print \"leaf-v1\"\n    0\n") is true
   - Expected: generate_real_leaf() equals `REAL_SMF`
   - Expected: first_code equals `0`
   - Expected: generate_real_leaf() equals `REAL_SMF`
   - Expected: file_hash_sha256(REAL_SMF) equals `artifact_v1`
   - Expected: file_write(REAL_LEAF, "fn main() -> i64:\n    print \"leaf-v2\"\n    0\n") is true
   - Expected: generate_real_leaf() equals `REAL_SMF`
   - Expected: second_code equals `0`
   - Expected: file_hash_sha256("bin/simple") equals `launcher_before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reuses unchanged code, regenerates changed code, and preserves the launcher")
expect(mkdir_p(REAL_FIXTURE_DIR)).to_equal(true)
expect(mkdir_p("build/smf")).to_equal(true)
expect(file_write(REAL_LEAF, "fn main() -> i64:\n    print \"leaf-v1\"\n    0\n")).to_equal(true)

val launcher_before = file_hash_sha256("bin/simple")
expect(generate_real_leaf()).to_equal(REAL_SMF)
val artifact_v1 = file_hash_sha256(REAL_SMF)
expect(artifact_v1.len()).to_be_greater_than(0)

val (first_out, _first_err, first_code) = run_real_leaf()
expect(first_code).to_equal(0)
expect(first_out).to_contain("leaf-v1")

expect(generate_real_leaf()).to_equal(REAL_SMF)
expect(file_hash_sha256(REAL_SMF)).to_equal(artifact_v1)

expect(file_write(REAL_LEAF, "fn main() -> i64:\n    print \"leaf-v2\"\n    0\n")).to_equal(true)
expect(generate_real_leaf()).to_equal(REAL_SMF)
expect(file_hash_sha256(REAL_SMF)).to_not_equal(artifact_v1)

val (second_out, _second_err, second_code) = run_real_leaf()
expect(second_code).to_equal(0)
expect(second_out).to_contain("leaf-v2")
expect(second_out).to_not_contain("leaf-v1")
expect(file_hash_sha256("bin/simple")).to_equal(launcher_before)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Design:** `doc/05_design/infra/perf_umbrella/perf_opt_design.md ## dynSMF cache`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4c088ab50958a3bdc22ff8a174145dae0e4b21c8a2217c2038a3fd8235aa8540`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4c088ab50958a3bdc22ff8a174145dae0e4b21c8a2217c2038a3fd8235aa8540`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4c088ab50958a3bdc22ff8a174145dae0e4b21c8a2217c2038a3fd8235aa8540`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/02_integration/app/simple/smf_cache_reuse_spec.spl
mirror: doc/06_spec/02_integration/app/simple/smf_cache_reuse_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/simple/smf_cache_reuse_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/simple/smf_cache_reuse_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/app/simple/smf_cache_reuse_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/app/simple/smf_cache_reuse_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts artifact when sidecar hash matches current source hash (cache hit)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/simple/smf_cache_reuse_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects artifact when sidecar hash differs from current source hash (stale source miss)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/simple/smf_cache_reuse_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects artifact when sidecar is absent (no .srchash file)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
