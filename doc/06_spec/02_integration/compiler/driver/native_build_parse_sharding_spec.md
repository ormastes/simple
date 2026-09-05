# Native Build Parse Sharding Specification

> Tests covering native-build parse sharding.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Build Parse Sharding Specification

## Scenarios

### native-build parse sharding

<details>
<summary>Advanced: splits a cold parse across shard processes and then parses nothing</summary>

#### splits a cold parse across shard processes and then parses nothing _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- splits a cold parse across shard processes and then parses nothing
   - Expected: dir_create_all(root) is true
   - Expected: code equals `0`
   - Expected: count_of(blob, "[parse-shard] done shard=") equals `2`
   - Expected: blob contains `[parse-shard] 2/2 shard(s) completed`
   - Expected: summary contains `hits=3`
   - Expected: summary contains `misses=0`
   - Expected: summary contains `parses=0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("splits a cold parse across shard processes and then parses nothing")
val run_id = getpid()
val root = "build/tmp/parse_shard_spec_{run_id}"
expect(dir_create_all(root)).to_equal(true)
val (blob, code) = run_build("{root}/cache", "{root}/fe", "{root}/out", "1", "1")
expect(code).to_equal(0)
# Both shards ran and reported.
expect(count_of(blob, "[parse-shard] done shard=")).to_equal(2)
expect(blob.contains("[parse-shard] 2/2 shard(s) completed")).to_equal(true)
# The REAL build's summary is the last one: every module already cached.
val summary = last_summary(blob)
expect(summary.contains("hits=3")).to_equal(true)
expect(summary.contains("misses=0")).to_equal(true)
expect(summary.contains("parses=0")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: produces a binary byte-identical to an unsharded, uncached build</summary>

#### produces a binary byte-identical to an unsharded, uncached build _(slow)_

- produces a binary byte-identical to an unsharded, uncached build
   - Expected: dir_create_all(root) is true
   - Expected: ca equals `0`
   - Expected: cb equals `0`
   - Expected: file_exists("{root}/sharded.bin") is true
   - Expected: file_exists("{root}/plain.bin") is true
   - Expected: file_read("{root}/sharded.bin") equals `file_read("{root}/plain.bin")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("produces a binary byte-identical to an unsharded, uncached build")
# Sharding may only change WHICH PROCESS parsed a module. If the bytes
# move, a restored parse is not the parse it replaced, and the whole
# design is unsound -- so this is the acceptance test, not a nicety.
val run_id = getpid()
val root = "build/tmp/parse_shard_ident_spec_{run_id}"
expect(dir_create_all(root)).to_equal(true)
val (_a, ca) = run_build("{root}/c1", "{root}/fe", "{root}/sharded.bin", "1", "1")
expect(ca).to_equal(0)
val (_b, cb) = run_build("{root}/c2", "{root}/fe2", "{root}/plain.bin", "0", "0")
expect(cb).to_equal(0)
expect(file_exists("{root}/sharded.bin")).to_equal(true)
expect(file_exists("{root}/plain.bin")).to_equal(true)
expect(file_read("{root}/sharded.bin")).to_equal(file_read("{root}/plain.bin"))
```

</details>


</details>

<details>
<summary>Advanced: claims modules from a shared work queue, each exactly once, and the real build hits them all</summary>

#### claims modules from a shared work queue, each exactly once, and the real build hits them all _(slow)_

- claims modules from a shared work queue, each exactly once, and the real build hits them all
   - Expected: dir_create_all(root) is true
   - Expected: code equals `0`
   - Expected: blob contains `[parse-shard] 2/2 shard(s) completed split=queue`
   - Expected: shard_lines equals `2`
   - Expected: claimed_total equals `3`
   - Expected: parsed_total equals `3`
   - Expected: last_summary(blob) contains `hits=3`
   - Expected: file_exists("{root}/fe/.lock") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("claims modules from a shared work queue, each exactly once, and the real build hits them all")
# The split is a shared work queue (claim markers under the frontend
# cache dir, flock'd), not a static hash slice: a static slice has a
# tail where the slowest slice gates the phase
# (doc/08_tracking/bug/native_build_phases_after_parse_single_threaded_2026-08-22.md).
# WHICH shard parses a module is now timing-dependent, so the old
# "same shard, same count, every run" pin is gone; the invariant that
# replaced it is the one that actually protects the output: every
# module is claimed by exactly one shard (claimed counts sum to N with
# no duplicates) and the real build then parses nothing.
val run_id = getpid()
val root = "build/tmp/parse_shard_queue_spec_{run_id}"
expect(dir_create_all(root)).to_equal(true)
val (blob, code) = run_build("{root}/cache", "{root}/fe", "{root}/out", "1", "1")
expect(code).to_equal(0)
expect(blob.contains("[parse-shard] 2/2 shard(s) completed split=queue")).to_equal(true)
var claimed_total: i64 = 0
var parsed_total: i64 = 0
var shard_lines = 0
for line in blob.split("\n"):
    if line.contains("[parse-shard] done shard="):
        shard_lines = shard_lines + 1
        for tok in line.trim().split(" "):
            if tok.starts_with("claimed="):
                claimed_total = claimed_total + (tok.substring(8).to_i64() ?? -100)
            elif tok.starts_with("parses="):
                parsed_total = parsed_total + (tok.substring(7).to_i64() ?? -100)
# Per-worker progress from BOTH workers, and the union is every module
# exactly once: a double claim would push the sum past 3, a lost one
# would leave it short.
expect(shard_lines).to_equal(2)
expect(claimed_total).to_equal(3)
expect(parsed_total).to_equal(3)
expect(last_summary(blob).contains("hits=3")).to_equal(true)
# The queue dir is private to the orchestrator and removed with it.
expect(file_exists("{root}/fe/.lock")).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: keeps the static hash split available behind SIMPLE_PARSE_SHARD_QUEUE=0</summary>

#### keeps the static hash split available behind SIMPLE_PARSE_SHARD_QUEUE=0 _(slow)_

- keeps the static hash split available behind SIMPLE_PARSE_SHARD_QUEUE=0
   - Expected: dir_create_all(root) is true
   - Expected: code equals `0`
   - Expected: blob contains `[parse-shard] 2/2 shard(s) completed split=static`
   - Expected: count_of(blob, "claimed=0") equals `2`
   - Expected: last_summary(blob) contains `hits=3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("keeps the static hash split available behind SIMPLE_PARSE_SHARD_QUEUE=0")
# Same output, same cache hits, just the old partition -- the knob is
# the escape hatch if the queue ever misbehaves on a host, so it must
# keep working rather than silently becoming the queue.
val run_id = getpid()
val root = "build/tmp/parse_shard_static_spec_{run_id}"
expect(dir_create_all(root)).to_equal(true)
rt_env_set("SIMPLE_PARSE_SHARD_QUEUE", "0")
val (blob, code) = run_build("{root}/cache", "{root}/fe", "{root}/out", "1", "1")
rt_env_set("SIMPLE_PARSE_SHARD_QUEUE", "")
expect(code).to_equal(0)
expect(blob.contains("[parse-shard] 2/2 shard(s) completed split=static")).to_equal(true)
expect(count_of(blob, "claimed=0")).to_equal(2)
expect(last_summary(blob).contains("hits=3")).to_equal(true)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/02_integration/compiler/driver/native_build_parse_sharding_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering native-build parse sharding.
- native-build parse sharding

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 4 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `64024c8d77b418e9148c21c5bc615923f31f64afcc700bb16238b39b4d77354c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `64024c8d77b418e9148c21c5bc615923f31f64afcc700bb16238b39b4d77354c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `64024c8d77b418e9148c21c5bc615923f31f64afcc700bb16238b39b4d77354c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/02_integration/compiler/driver/native_build_parse_sharding_spec.spl
mirror: doc/06_spec/02_integration/compiler/driver/native_build_parse_sharding_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/compiler/driver/native_build_parse_sharding_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/compiler/driver/native_build_parse_sharding_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/compiler/driver/native_build_parse_sharding_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/compiler/driver/native_build_parse_sharding_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'splits a cold parse across shard processes and then parses nothing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/compiler/driver/native_build_parse_sharding_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces a binary byte-identical to an unsharded, uncached build' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/compiler/driver/native_build_parse_sharding_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'claims modules from a shared work queue, each exactly once, and the real build hits them all' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
