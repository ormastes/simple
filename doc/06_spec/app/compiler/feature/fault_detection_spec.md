# Fault Detection Specification

**Feature ID:** #FAULT-001 to #FAULT-020 | **Category:** Runtime | Safety | **Difficulty:** 3/5 | **Status:** Implemented

_Source: `test/feature/app/fault_detection_spec.spl`_

---

## Overview

The Simple runtime includes fault detection for stack overflow, timeout,
and execution limits. All features are toggleable via CLI flags, FFI calls,
or the `sys.fault_detection` stdlib module.

## Syntax

```simple
use std.sys.fault_detection.*

# High-level API
enable_stack_overflow_detection()
set_recursion_limit(500)
set_timeout(30)
set_execution_limit(5000000)
reset_defaults()

# Config-based API
val config = FaultConfig__strict()
config.apply()
```

## Key Concepts

| Feature | Default | Purpose |
|---------|---------|---------|
| Stack overflow detection | debug=on | Recursion depth check |
| Max recursion depth | 1000 | Max call depth before error |
| Timeout | 0 (off) | Wall-clock timeout in seconds |
| Execution limit | 10000000 | Instruction count limit |

## Behavior

- Stack overflow detection tracks call depth with atomic counters
- Timeout uses a watchdog thread that checks every 100ms
- Execution limit counts instructions at loop back-edges
- All features have zero or near-zero overhead when disabled

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 36 |

## Test Structure

### Fault Detection - FFI API

#### stack overflow detection

- ✅ enables detection and allows shallow recursion
- ✅ allows zero-depth call
- ✅ allows single recursion step
- ✅ works when disabled
#### depth limit configuration

- ✅ accepts small depth limit
- ✅ accepts large depth limit
#### timeout configuration

- ✅ disables timeout with zero
- ✅ sets large timeout without affecting fast code
#### execution limit configuration

- ✅ sets execution limit
- ✅ disables execution limit with zero
### Fault Detection - Simple API

#### enable/disable stack overflow

- ✅ enables detection
- ✅ disables detection
#### set_recursion_limit

- ✅ sets a custom limit
#### set_timeout

- ✅ sets and clears timeout
#### set_execution_limit

- ✅ sets a custom limit
#### reset_defaults

- ✅ restores default configuration
### Fault Detection - FaultConfig

#### preset configurations

- ✅ creates default config
- ✅ creates strict config
- ✅ creates permissive config
- ✅ creates disabled config
#### config application

- ✅ applies default config
- ✅ applies strict config
- ✅ applies permissive config
- ✅ applies disabled config and re-enables
#### config builders

- ✅ creates config with custom timeout
- ✅ creates config with custom depth
- ✅ creates config with custom execution limit
- ✅ chains multiple builders
### Fault Detection - Constants

- ✅ has correct default max recursion depth
- ✅ has correct default execution limit
- ✅ has correct default timeout
### Fault Detection - Functional

#### recursion with detection enabled

- ✅ handles fibonacci computation
- ✅ handles multiple sequential recursive calls
#### iterative with detection enabled

- ✅ handles iterative loops
#### toggling detection during computation

- ✅ toggle on-off-on preserves correctness
#### combined features

- ✅ all features active with fast code

