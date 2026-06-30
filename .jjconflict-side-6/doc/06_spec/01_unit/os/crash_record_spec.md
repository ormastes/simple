# Crash Record Specification

> <details>

<!-- sdn-diagram:id=crash_record_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=crash_record_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

crash_record_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=crash_record_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Crash Record Specification

## Scenarios

### CrashRecord

#### is_fatal for trap

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rec("trap", 132, 0).is_fatal()).to_equal(true)
```

</details>

#### is_fatal for abort

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rec("abort", 134, 0).is_fatal()).to_equal(true)
```

</details>

#### is_fatal for invariant_violation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rec("invariant_violation", 1, 0).is_fatal()).to_equal(true)
```

</details>

#### not fatal for panic

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rec("panic", 101, 0).is_fatal()).to_equal(false)
```

</details>

#### not fatal for timeout

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rec("timeout", 124, 0).is_fatal()).to_equal(false)
```

</details>

#### not fatal for clean_exit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rec("clean_exit", 0, 0).is_fatal()).to_equal(false)
```

</details>

#### summary includes reason and exit code

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = rec("panic", 101, 2).summary()
expect(s).to_contain("panic")
expect(s).to_contain("101")
expect(s).to_contain("2")
```

</details>

### CrashLog

#### starts empty

1. var log = CrashLog create
   - Expected: log.count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var log = CrashLog.create("worker")
expect(log.count()).to_equal(0)
```

</details>

#### add increases count

1. var log = CrashLog create
2. log add
   - Expected: log.count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var log = CrashLog.create("worker")
log.add(rec("panic", 101, 0))
expect(log.count()).to_equal(1)
```

</details>

#### last returns most recent

1. var log = CrashLog create
2. log add
3. log add


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var log = CrashLog.create("worker")
log.add(rec("panic", 101, 0))
log.add(rec("timeout", 124, 1))
val last = log.last()
match last:
    Some(r): expect(r.reason).to_equal("timeout")
    nil: expect("should not be nil").to_equal("")
```

</details>

#### last returns nil when empty

1. var log = CrashLog create


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var log = CrashLog.create("worker")
val last = log.last()
expect(last).to_be_nil()
```

</details>

#### recent returns N items

1. var log = CrashLog create
2. log add
3. log add
4. log add
   - Expected: r.len() equals `2`
   - Expected: r[0].reason equals `b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var log = CrashLog.create("worker")
log.add(rec("a", 1, 0))
log.add(rec("b", 2, 1))
log.add(rec("c", 3, 2))
val r = log.recent(2)
expect(r.len()).to_equal(2)
expect(r[0].reason).to_equal("b")
```

</details>

#### recent returns all when N exceeds count

1. var log = CrashLog create
2. log add
   - Expected: log.recent(10).len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var log = CrashLog.create("worker")
log.add(rec("a", 1, 0))
expect(log.recent(10).len()).to_equal(1)
```

</details>

#### trims when over max

1. var log = CrashLog
2. log add
3. log add
4. log add
5. log add
   - Expected: log.count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var log = CrashLog(component_id: "w", records: [], max_records: 3)
log.add(rec("a", 1, 0))
log.add(rec("b", 2, 1))
log.add(rec("c", 3, 2))
log.add(rec("d", 4, 3))
expect(log.count()).to_equal(3)
val last = log.last()
match last:
    Some(r): expect(r.reason).to_equal("d")
    nil: expect("should not be nil").to_equal("")
```

</details>

#### has_fatal detects fatal records

1. var log = CrashLog create
2. log add
3. log add
   - Expected: log.has_fatal() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var log = CrashLog.create("worker")
log.add(rec("panic", 101, 0))
log.add(rec("trap", 132, 1))
expect(log.has_fatal()).to_equal(true)
```

</details>

#### has_fatal returns false with no fatals

1. var log = CrashLog create
2. log add
3. log add
   - Expected: log.has_fatal() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var log = CrashLog.create("worker")
log.add(rec("panic", 101, 0))
log.add(rec("timeout", 124, 1))
expect(log.has_fatal()).to_equal(false)
```

</details>

#### crashes_in_window counts records

1. var log = CrashLog create
2. log add
3. log add
   - Expected: log.count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var log = CrashLog.create("worker")
log.add(rec("a", 1, 0))
log.add(rec("b", 2, 1))
expect(log.count()).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crash_record_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- CrashRecord
- CrashLog

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
