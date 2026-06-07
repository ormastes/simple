# Supervisor Specification

> <details>

<!-- sdn-diagram:id=supervisor_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=supervisor_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

supervisor_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=supervisor_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Supervisor Specification

## Scenarios

### Supervisor stdlib

### constants

#### restart strategies are defined

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(RESTART_PERMANENT).to_equal("permanent")
expect(RESTART_TEMPORARY).to_equal("temporary")
expect(RESTART_TRANSIENT).to_equal("transient")
```

</details>

#### supervisor strategies are defined

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(STRATEGY_ONE_FOR_ONE).to_equal("one_for_one")
expect(STRATEGY_ONE_FOR_ALL).to_equal("one_for_all")
```

</details>

### supervisor_config_default

#### creates default config

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = supervisor_config_default()
expect(config.strategy).to_equal("one_for_one")
expect(config.max_restarts).to_equal(3)
expect(config.max_seconds).to_equal(5)
```

</details>

### child_spec

#### creates child spec with id

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cs = child_spec("worker1")
expect(cs.id).to_equal("worker1")
expect(cs.restart).to_equal("permanent")
```

</details>

### supervisor_new

#### creates supervisor with strategy

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sup = supervisor_new(STRATEGY_ONE_FOR_ONE)
expect(sup.is_running()).to_equal(false)
expect(sup.child_count()).to_equal(0)
expect(sup.config.strategy).to_equal("one_for_one")
```

</details>

### adding and removing children

#### adds a child

1. sup add child
   - Expected: sup.child_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sup = supervisor_new(STRATEGY_ONE_FOR_ONE)
sup.add_child(child_spec("worker1"))
expect(sup.child_count()).to_equal(1)
```

</details>

#### removes a child

1. sup add child
2. sup add child
3. sup remove child
   - Expected: sup.child_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sup = supervisor_new(STRATEGY_ONE_FOR_ONE)
sup.add_child(child_spec("worker1"))
sup.add_child(child_spec("worker2"))
sup.remove_child("worker1")
expect(sup.child_count()).to_equal(1)
```

</details>

### start and stop

#### starts the supervisor

1. sup start
   - Expected: sup.is_running() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sup = supervisor_new(STRATEGY_ONE_FOR_ONE)
sup.start()
expect(sup.is_running()).to_equal(true)
```

</details>

#### stops the supervisor

1. sup start
2. sup stop
   - Expected: sup.is_running() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sup = supervisor_new(STRATEGY_ONE_FOR_ONE)
sup.start()
sup.stop()
expect(sup.is_running()).to_equal(false)
```

</details>

### restart tracking

#### records restart count

1. sup add child
2. sup record restart
3. sup record restart
   - Expected: sup.restart_count("worker1") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sup = supervisor_new(STRATEGY_ONE_FOR_ONE)
sup.add_child(child_spec("worker1"))
sup.record_restart("worker1")
sup.record_restart("worker1")
expect(sup.restart_count("worker1")).to_equal(2)
```

</details>

#### checks within restart limits

1. sup add child
   - Expected: sup.within_limits() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sup = supervisor_new(STRATEGY_ONE_FOR_ONE)
sup.add_child(child_spec("worker1"))
expect(sup.within_limits()).to_equal(true)
```

</details>

#### should_restart returns true for permanent

1. sup add child
   - Expected: sup.should_restart("worker1") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sup = supervisor_new(STRATEGY_ONE_FOR_ONE)
sup.add_child(child_spec("worker1"))
expect(sup.should_restart("worker1")).to_equal(true)
```

</details>

#### should_restart returns false for temporary

1. sup add child
   - Expected: sup.should_restart("temp_worker") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sup = supervisor_new(STRATEGY_ONE_FOR_ONE)
sup.add_child(child_spec_with_restart("temp_worker", RESTART_TEMPORARY))
expect(sup.should_restart("temp_worker")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/supervisor_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Supervisor stdlib
- constants
- supervisor_config_default
- child_spec
- supervisor_new
- adding and removing children
- start and stop
- restart tracking

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
