# @req REQ-TESTRUNNER-DAEMON-BACKLOG-BYPASS

> Light-daemon backlog bypass — when a test client must NOT join the queue.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @req REQ-TESTRUNNER-DAEMON-BACKLOG-BYPASS

Light-daemon backlog bypass — when a test client must NOT join the queue.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test_runner_new/daemon_backlog_bypass_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Light-daemon backlog bypass — when a test client must NOT join the queue.

Audience: anyone editing `src/app/test_runner_new/daemon_backlog.spl`,
`test_runner_client.spl`'s bypass ladder, or `src/app/test_daemon/light_daemon.spl`.

Why this spec exists (REPRODUCER). Before 2026-08-17 a `bin/simple test <spec>`
unconditionally submitted its spec to the process-global light daemon at
`.build/test_daemon_light/` and waited. That daemon runs ONE worker draining a
FIFO, and each `handle_request` blocks for up to the served spec's whole budget
(600s cap), so on a host with several concurrent sessions a client paid every
queued spec's runtime before its own started. The bypass decision did not exist
at all — `daemon_backlog_bypass` was undefined, so this spec could not compile,
let alone pass.

The purchase was zero. Measured 2026-08-17 by `strace -f -e trace=openat` on the
same spec, counting distinct `src/**.spl` modules opened: the direct lane opens
77, the daemon's per-request worker opens 78. The daemon forks a cold child
every time; its amortization factor is 1.0.

Assertions here are ALGORITHMIC (decision as a function of queue depth), never
wall-clock — wall clock on this host is a contention artifact.

## Scenarios

### light-daemon backlog bypass

### the decision as a function of queue depth

#### takes the daemon lane when the queue is empty

- takes the daemon lane when the queue is empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("takes the daemon lane when the queue is empty")
expect(daemon_backlog_bypass(0)).to_be_false()
```

</details>

#### bypasses as soon as one request is already queued

- bypasses as soon as one request is already queued


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("bypasses as soon as one request is already queued")
# One queued request is one full spec runtime of serial
# head-of-line blocking, and the direct lane runs the same child.
expect(daemon_backlog_bypass(1)).to_be_true()
```

</details>

#### keeps bypassing as the queue grows

- keeps bypassing as the queue grows


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps bypassing as the queue grows")
expect(daemon_backlog_bypass(2)).to_be_true()
expect(daemon_backlog_bypass(17)).to_be_true()
```

</details>

#### is monotone: a deeper queue never re-enables the daemon

- is monotone: a deeper queue never re-enables the daemon


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("is monotone: a deeper queue never re-enables the daemon")
var depth = 0
var seen_bypass = false
while depth <= 12:
    val decision = daemon_backlog_bypass(depth)
    if seen_bypass:
        expect(decision).to_be_true()
    if decision:
        seen_bypass = true
    depth = depth + 1
expect(seen_bypass).to_be_true()
```

</details>

#### treats an unknown/absent queue as empty rather than inventing a failure

- treats an unknown/absent queue as empty rather than inventing a failure


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("treats an unknown/absent queue as empty rather than inventing a failure")
# The client reports 0 when the request directory is unreadable;
# negative depths must not flip the decision either.
expect(daemon_backlog_bypass(-1)).to_be_false()
```

</details>

#### uses the smallest threshold that can exist

- uses the smallest threshold that can exist
   - Expected: LIGHT_DAEMON_BACKLOG_BYPASS_THRESHOLD equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("uses the smallest threshold that can exist")
# There is no depth at which queueing behind a single serial worker
# is cheaper than running the identical child directly, so the
# threshold must not drift upward into 'a little queueing is fine'.
expect(LIGHT_DAEMON_BACKLOG_BYPASS_THRESHOLD).to_equal(1)
```

</details>

### counting pending requests from a directory listing

#### counts .req entries

- counts .req entries
   - Expected: count_pending_requests(["a.req", "b.req"]) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("counts .req entries")
expect(count_pending_requests(["a.req", "b.req"])).to_equal(2)
```

</details>

#### reports an empty listing as zero

- reports an empty listing as zero
   - Expected: count_pending_requests([]) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("reports an empty listing as zero")
expect(count_pending_requests([])).to_equal(0)
```

</details>

#### ignores the atomic-write .req.tmp staging files

- ignores the atomic-write .req.tmp staging files
   - Expected: count_pending_requests(["a.req.tmp"]) equals `0`
   - Expected: count_pending_requests(["a.req", "b.req.tmp"]) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("ignores the atomic-write .req.tmp staging files")
# atomic_write_text writes <path>.tmp then renames. Counting the
# tmp file would make a client bypass on an in-flight write that is
# about to become its OWN request.
expect(count_pending_requests(["a.req.tmp"])).to_equal(0)
expect(count_pending_requests(["a.req", "b.req.tmp"])).to_equal(1)
```

</details>

#### ignores unrelated entries left in the lane directory

- ignores unrelated entries left in the lane directory
   - Expected: count_pending_requests(["daemon.lock", "daemon.binary", "x.resp"]) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("ignores unrelated entries left in the lane directory")
expect(count_pending_requests(["daemon.lock", "daemon.binary", "x.resp"])).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
- `REQ-TESTRUNNER-DAEMON-BACKLOG-BYPASS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `64b6911c6727c54be65638f3e88ee5f5b83ecf6eac48ac3c7b5532e326d29518`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `64b6911c6727c54be65638f3e88ee5f5b83ecf6eac48ac3c7b5532e326d29518`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `64b6911c6727c54be65638f3e88ee5f5b83ecf6eac48ac3c7b5532e326d29518`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/app/test_runner_new/daemon_backlog_bypass_spec.spl
mirror: doc/06_spec/01_unit/app/test_runner_new/daemon_backlog_bypass_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/test_runner_new/daemon_backlog_bypass_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/test_runner_new/daemon_backlog_bypass_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/test_runner_new/daemon_backlog_bypass_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/test_runner_new/daemon_backlog_bypass_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'takes the daemon lane when the queue is empty' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/test_runner_new/daemon_backlog_bypass_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bypasses as soon as one request is already queued' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/test_runner_new/daemon_backlog_bypass_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps bypassing as the queue grows' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
