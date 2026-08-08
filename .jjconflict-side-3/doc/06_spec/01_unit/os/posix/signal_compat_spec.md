# POSIX signal_compat Specification

> Verifies signal registration, masking, pending-tracking, and the

<!-- sdn-diagram:id=signal_compat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=signal_compat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

signal_compat_spec -> std
signal_compat_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=signal_compat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/01_unit/os/posix/signal_compat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies signal registration, masking, pending-tracking, and the
`signal_deliver` alias used by PM's extern.

## Scenarios

### posix_sigprocmask

#### SIG_BLOCK sets mask bits

1. posix sigprocmask


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prev = posix_sigprocmask(0, 0b1010)
val now  = posix_sigprocmask(0, 0)
expect (now & 0b1010u64).to_equal(0b1010u64)
posix_sigprocmask(2, 0)  # reset to empty
```

</details>

#### SIG_UNBLOCK clears mask bits

1. posix sigprocmask
2. posix sigprocmask
3. posix sigprocmask


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
posix_sigprocmask(2, 0b1111)
posix_sigprocmask(1, 0b0010)
val after = posix_sigprocmask(2, 0)
expect (after & 0b0010u64).to_equal(0u64)
posix_sigprocmask(2, 0)
```

</details>

#### SIG_SETMASK replaces mask wholesale

1. posix sigprocmask
2. posix sigprocmask


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
posix_sigprocmask(2, 0xFF)
val after = posix_sigprocmask(2, 0x01)
expect (after & 0x01u64).to_equal(0x01u64)
posix_sigprocmask(2, 0)
```

</details>

#### SIGKILL cannot be blocked

1. posix sigprocmask
2. posix sigprocmask


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
posix_sigprocmask(2, 0xFFFFFFFFu64)
val now = posix_sigprocmask(2, 0xFFFFFFFFu64)
val kill_bit: u64 = 1u64 << 9u64
expect (now & kill_bit).to_equal(0u64)
posix_sigprocmask(2, 0)
```

</details>

### signal_raise + signal_is_pending

#### raises a signal into the pending set

1. posix sigprocmask
2. signal raise


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
posix_sigprocmask(2, 0)
signal_raise(SIGUSR1)
expect signal_is_pending(SIGUSR1).to_equal(true)
```

</details>

#### returns false for out-of-range signum

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect signal_is_pending(0).to_equal(false)
expect signal_is_pending(1000).to_equal(false)
```

</details>

### signal_deliver alias
_signal_deliver is a thin rename PM's extern expects._

#### signal_deliver returns an i32 (zero or negative errno)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = signal_deliver(1u64, SIGUSR1)
val bounded: bool = r <= 0
expect bounded.to_equal(true)
```

</details>

### signal_queue_has_pending

#### empty queue reports false

1. posix sigprocmask
2. signal deliver pending


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
posix_sigprocmask(2, 0)
# Drain any pending from earlier cases.
signal_deliver_pending()
val any = signal_queue_has_pending(1u64)
expect any.to_equal(false)
```

</details>

#### blocked signal does not count as pending

1. posix sigprocmask
2. posix sigprocmask
3. signal raise
4. posix sigprocmask
5. signal deliver pending


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
