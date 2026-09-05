# Simple Build/Test Abnormality Detection

This manual describes the operator-visible contract for performance and memory abnormality decisions. It separates machine protection, declared budgets, and historical comparisons so that one mechanism cannot silently weaken another.

## Trustworthy resource evidence

### Measure a real owned child tree

1. Create a bounded execution resource scope.
2. Run a child and grandchild through the production facade.
3. Require retained exit status, tree charge, and peak-process evidence.

On Unix, the fallback samples the owned process group and reports that lower-quality rung explicitly. It does not relabel sampled charge as exact cgroup accounting.

### Prove a wall watchdog with a real child

1. Create a scope with a short wall deadline.
2. Run a child that exceeds it.
3. Require affirmative watchdog evidence and `WallTimeout` classification.

### Preserve SIGSEGV as a crash signal

1. Run a real child that raises SIGSEGV.
2. Retain signal 11.
3. Require `Signal`, not `MemoryMax`, when no provider memory event exists.

### Classify only affirmative termination evidence

1. Create a bounded execution resource scope.
2. Run a child tree and collect resource evidence.
3. Classify termination from affirmative evidence.

The retained exit code and signal are observations, not proof of timeout or memory exhaustion. A SIGSEGV without a provider memory event remains a crash signal.

### Prove a memory budget event from scope counters

1. Create a bounded execution resource scope.
2. Capture the scope’s memory event counters before and after execution.
3. Run a child tree and collect resource evidence.
4. Classify termination from affirmative evidence.

An increase in `memory.max`, `oom`, or `oom_kill` is affirmative scope evidence. Exit 137 remains only a retained status when those counters do not change.

### Prove a live Linux memory kill

1. Create a delegated service scope with a 32 MiB `MemoryMax`.
2. Run a child that allocates 128 MiB.
3. Read the retained service result, main-code/status, and memory peak.
4. Require `oom-kill`, signal 9, and `MemoryMax` classification.

This row is Linux/systemd-specific. A generic systemd `resources` result is not enough to identify a CPU or PID limit and is deliberately left unverified.

### Prove a live Linux PID limit

1. Run a fork fixture under `TasksMax=4`.
2. Read the cgroup's `pids.events` counter before and after the fixture while the delegated supervisor still owns the scope.
3. Require an increased `max` counter before classifying `ProcessLimit`.

### Record a supervisor-requested external termination

1. Start a real child under the delegated supervisor.
2. Have that supervisor request SIGTERM and emit its private receipt marker.
3. Require `ExternalTermination` and signal 15; a bare 143 exit remains insufficient evidence.

### Detect a confirmed regression while preserving its approved baseline

1. Record spans and work counters.
2. Compare against an approved cohort baseline.
3. Explain the budget and anomaly decisions.

The comparison requires compatible cohort identity, complete required spans, an explicit approved baseline, absolute and relative floors, robust MAD noise, and confirmation for failure. Recording or comparing the candidate leaves the approved generation unchanged.

### Detect missing phases and quadratic work before timeout

1. Record spans and work counters.
2. Require the scenario’s stable phase set.
3. Evaluate N/2N/4N/8N work with the configured maximum growth exponent.
4. Explain the budget and anomaly decisions.

A missing required phase invalidates an apparent speedup. A growth exponent above the selected bound is a complexity regression even when no wall timeout has occurred.

### Retain a rare spike and explain incremental invalidation

1. Retain all five samples, including the rare maximum.
2. Report the maximum and outlier count.
3. Require a non-empty invalidation reason when the incremental cache invalidates work.

## Requirement traceability

- REQ-001/002/003/004/013: real owned-tree scope, explicit evidence quality, and affirmative termination classification.
- REQ-008/009: frozen approved baseline and robust confirmed regression decision.
- REQ-009/010/012: tail retention, incremental evidence, required phases, and complexity probes.

Windows Job Object and macOS-native receipt rows remain blocked in the system-test plan until they run on those hosts. They are not represented as passing by Linux evidence.
