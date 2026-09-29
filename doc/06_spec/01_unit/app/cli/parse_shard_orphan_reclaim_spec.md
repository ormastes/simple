# Parse Shard Orphan Reclaim Specification

> Tests covering parse shard orphan reclaim.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parse Shard Orphan Reclaim Specification

## Scenarios

### parse shard orphan reclaim

#### releases exactly the claims owned by a dead shard (simulated death after claim)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- releases exactly the claims owned by a dead shard (simulated death after claim)
   - Expected: released equals `2`
   - Expected: file_read("{dir}/333-18.claim") equals `1/8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("releases exactly the claims owned by a dead shard (simulated death after claim)")
val dir = fresh_queue("dead")
expect(file_write("{dir}/111-20.claim", "6/8")).to_be_true()
expect(file_write("{dir}/222-31.claim", "6/8")).to_be_true()
expect(file_write("{dir}/333-18.claim", "1/8")).to_be_true()
expect(file_write("{dir}/.lock", "")).to_be_true()
val released = parse_shard_release_claims(dir, ["6/8"])
expect(released).to_equal(2)
expect(file_exists("{dir}/111-20.claim")).to_be_false()
expect(file_exists("{dir}/222-31.claim")).to_be_false()
expect(file_exists("{dir}/333-18.claim")).to_be_true()
expect(file_read("{dir}/333-18.claim")).to_equal("1/8")
expect(file_exists("{dir}/.lock")).to_be_true()
val _c = dir_remove_all(dir)
```

</details>

#### releases nothing when no shard died or the queue is unpublished

- releases nothing when no shard died or the queue is unpublished
   - Expected: parse_shard_release_claims(dir, []) equals `0`
   - Expected: parse_shard_release_claims("", ["0/8"]) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("releases nothing when no shard died or the queue is unpublished")
val dir = fresh_queue("alive")
expect(file_write("{dir}/111-20.claim", "0/8")).to_be_true()
expect(parse_shard_release_claims(dir, [])).to_equal(0)
expect(parse_shard_release_claims("", ["0/8"])).to_equal(0)
expect(file_exists("{dir}/111-20.claim")).to_be_true()
val _c = dir_remove_all(dir)
```

</details>

#### releases claims of several dead shards in one pass

- releases claims of several dead shards in one pass
   - Expected: parse_shard_release_claims(dir, ["2/4", "3/4"]) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("releases claims of several dead shards in one pass")
val dir = fresh_queue("multi")
expect(file_write("{dir}/1-1.claim", "2/4")).to_be_true()
expect(file_write("{dir}/2-1.claim", "3/4")).to_be_true()
expect(file_write("{dir}/3-1.claim", "0/4")).to_be_true()
expect(parse_shard_release_claims(dir, ["2/4", "3/4"])).to_equal(2)
expect(file_exists("{dir}/3-1.claim")).to_be_true()
val _c = dir_remove_all(dir)
```

</details>

#### labels every rt_process_wait outcome so a dead shard is never silent

- labels every rt_process_wait outcome so a dead shard is never silent
   - Expected: parse_shard_exit_label(0) equals `exit=0`
   - Expected: parse_shard_exit_label(1) equals `exit=1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("labels every rt_process_wait outcome so a dead shard is never silent")
expect(parse_shard_exit_label(0)).to_equal("exit=0")
expect(parse_shard_exit_label(1)).to_equal("exit=1")
expect(parse_shard_exit_label(-1).contains("SIGNAL")).to_be_true()
expect(parse_shard_exit_label(-2).contains("TIMEOUT")).to_be_true()
```

</details>

#### orchestrator logs each shard's exit and reclaims before declaring the phase done

- orchestrator logs each shard's exit and reclaims before declaring the phase done


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("orchestrator logs each shard's exit and reclaims before declaring the phase done")
val src = file_read("src/app/cli/native_build_main.spl")
val log_at = src.index_of("FAILED \{parse_shard_exit_label(code)\}")
val reclaim_at = src.index_of("parse_shard_release_claims(queue_dir, dead_specs)")
val retry_at = src.index_of("spawn_parse_shards(base, failed, count")
val done_at = src.index_of("shard(s) completed split=\{mode\}")
expect(log_at > 0).to_be_true()
expect(reclaim_at > 0).to_be_true()
expect(retry_at > reclaim_at).to_be_true()
expect(done_at > retry_at).to_be_true()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli/parse_shard_orphan_reclaim_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering parse shard orphan reclaim.
- parse shard orphan reclaim

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `09415a62e928b0ec1f81238c03685064fcf1027ba881d0b5476f7244dcf33ce3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `09415a62e928b0ec1f81238c03685064fcf1027ba881d0b5476f7244dcf33ce3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `09415a62e928b0ec1f81238c03685064fcf1027ba881d0b5476f7244dcf33ce3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/app/cli/parse_shard_orphan_reclaim_spec.spl
mirror: doc/06_spec/01_unit/app/cli/parse_shard_orphan_reclaim_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/cli/parse_shard_orphan_reclaim_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/cli/parse_shard_orphan_reclaim_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/cli/parse_shard_orphan_reclaim_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/cli/parse_shard_orphan_reclaim_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'releases exactly the claims owned by a dead shard (simulated death after claim)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/cli/parse_shard_orphan_reclaim_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'releases nothing when no shard died or the queue is unpublished' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/cli/parse_shard_orphan_reclaim_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'releases claims of several dead shards in one pass' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
