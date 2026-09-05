# POSIX signal_compat Specification

> Verifies signal registration, masking, pending-tracking, and the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# POSIX signal_compat Specification

Verifies signal registration, masking, pending-tracking, and the

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #WAVE2-G6 |
| Category | POSIX shim |
| Status | In Progress |
| Source | `test/unit/os/posix/signal_compat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies signal registration, masking, pending-tracking, and the
`signal_deliver` alias used by PM's extern.

## Scenarios

### posix_sigprocmask

#### SIG_BLOCK sets mask bits

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- SIG_BLOCK sets mask bits


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SIG_BLOCK sets mask bits")
val prev = posix_sigprocmask(0, 0b1010)
val now  = posix_sigprocmask(0, 0)
expect (now & 0b1010u64).to_equal(0b1010u64)
posix_sigprocmask(2, 0)  # reset to empty
```

</details>

#### SIG_UNBLOCK clears mask bits

- SIG_UNBLOCK clears mask bits


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SIG_UNBLOCK clears mask bits")
posix_sigprocmask(2, 0b1111)
posix_sigprocmask(1, 0b0010)
val after = posix_sigprocmask(2, 0)
expect (after & 0b0010u64).to_equal(0u64)
posix_sigprocmask(2, 0)
```

</details>

#### SIG_SETMASK replaces mask wholesale

- SIG_SETMASK replaces mask wholesale


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SIG_SETMASK replaces mask wholesale")
posix_sigprocmask(2, 0xFF)
val after = posix_sigprocmask(2, 0x01)
expect (after & 0x01u64).to_equal(0x01u64)
posix_sigprocmask(2, 0)
```

</details>

#### SIGKILL cannot be blocked

- SIGKILL cannot be blocked


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SIGKILL cannot be blocked")
posix_sigprocmask(2, 0xFFFFFFFFu64)
val now = posix_sigprocmask(2, 0xFFFFFFFFu64)
val kill_bit: u64 = 1u64 << 9u64
expect (now & kill_bit).to_equal(0u64)
posix_sigprocmask(2, 0)
```

</details>

### signal_raise + signal_is_pending

#### raises a signal into the pending set

- raises a signal into the pending set


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("raises a signal into the pending set")
posix_sigprocmask(2, 0)
signal_raise(SIGUSR1)
expect signal_is_pending(SIGUSR1).to_equal(true)
```

</details>

#### returns false for out-of-range signum

- returns false for out-of-range signum


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for out-of-range signum")
expect signal_is_pending(0).to_equal(false)
expect signal_is_pending(1000).to_equal(false)
```

</details>

### signal_deliver alias
_signal_deliver is a thin rename PM's extern expects._

#### signal_deliver returns an i32 (zero or negative errno)

- signal_deliver returns an i32 (zero or negative errno)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("signal_deliver returns an i32 (zero or negative errno)")
"""Covers the alias's calling convention."""
val r = signal_deliver(1u64, SIGUSR1)
val bounded: bool = r <= 0
expect bounded.to_equal(true)
```

</details>

### signal_queue_has_pending

#### empty queue reports false

- empty queue reports false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty queue reports false")
posix_sigprocmask(2, 0)
# Drain any pending from earlier cases.
signal_deliver_pending()
val any = signal_queue_has_pending(1u64)
expect any.to_equal(false)
```

</details>

#### blocked signal does not count as pending

- blocked signal does not count as pending


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocked signal does not count as pending")
posix_sigprocmask(2, 0)
val block_usr1: u64 = 1u64 << (SIGUSR1 as u64)
posix_sigprocmask(0, block_usr1)
signal_raise(SIGUSR1)
val any_while_blocked = signal_queue_has_pending(1u64)
expect any_while_blocked.to_equal(false)
posix_sigprocmask(2, 0)
signal_deliver_pending()
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `95a9c9a91e3d65d52f8390d27e4162296e07153ae8949850b23ffb5dcec6e901`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `95a9c9a91e3d65d52f8390d27e4162296e07153ae8949850b23ffb5dcec6e901`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `95a9c9a91e3d65d52f8390d27e4162296e07153ae8949850b23ffb5dcec6e901`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/posix/signal_compat_spec.spl
mirror: doc/06_spec/unit/os/posix/signal_compat_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/posix/signal_compat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/posix/signal_compat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/posix/signal_compat_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SIG_BLOCK sets mask bits' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/posix/signal_compat_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SIG_UNBLOCK clears mask bits' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/posix/signal_compat_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SIG_SETMASK replaces mask wholesale' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
