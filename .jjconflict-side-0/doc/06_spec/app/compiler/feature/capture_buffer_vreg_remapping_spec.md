# Capture Buffer and Virtual Register Remapping Specification

**Feature ID:** #VREGMAP-001 to #VREGMAP-020 | **Category:** Runtime | Memory Management | **Difficulty:** 4/5 | **Status:** Planned

_Source: `test/feature/usage/capture_buffer_vreg_remapping_spec.spl`_

---

## Overview

This specification covers advanced virtual register (vreg) remapping and capture
buffer management at the runtime level. These are internal optimization features
that affect how the interpreter manages memory and registers during function
execution.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Virtual Register (vreg) | Compiler-internal register representing values during execution |
| Capture Buffer | Runtime buffer capturing values into closure/lambda scopes |
| Remapping | Optimization to reuse vregs across code regions |
| Live Range | Set of instructions where a vreg is actively used |
| Interference | Two vregs conflict if their live ranges overlap |

## Behavior

- Virtual registers are allocated for each value in the program
- Capture buffers copy values from outer scope into closure scope
- Remapping allows vregs to be reused when live ranges don't overlap
- Optimization reduces memory pressure and improves cache locality
- All changes are transparent to the user - language behavior unchanged

## Related Specifications

- [Closures and Lambdas](closures_spec.spl) - Capture semantics
- [Memory Management](memory_management_spec.spl) - GC and allocation
- [Function Calls](function_calls_spec.spl) - Call conventions

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 46 |

## Test Structure

### Capture Buffer Creation

- ✅ creates capture buffer for single captured variable
- ✅ creates capture buffer for multiple variables
- ✅ captures variable in nested closure
- ✅ captures in lambda with parameters
### Capture Buffer Scope Isolation

- ✅ captures value at definition time
- ✅ captures in loop iteration
- ✅ captures different scopes separately
### Virtual Register Allocation

- ✅ allocates vreg for simple variable
- ✅ allocates vreg for expression result
- ✅ allocates vregs for multiple values
- ✅ allocates vreg for array element
### Virtual Register Reuse

- ✅ reuses vreg in sequential statements
- ✅ reuses vreg after value is no longer needed
- ✅ does not reuse interfering vregs
- ✅ reuses vregs in branches
### Live Range Analysis

- ✅ detects live range of simple variable
- ✅ detects live range extends to final use
- ✅ detects live range ends after last use
- ✅ handles nested live ranges
### Register Remapping in Loops

- ✅ remaps vregs in loop iterations
- ✅ handles nested loops with remapping
- ✅ preserves values across loop iterations
### Capture Buffer with Remapped Registers

- ✅ captures value despite vreg reuse
- ✅ captures multiple values with remapping
- ✅ captures in loop with vreg remapping
### Register Interference Detection

- ✅ detects interference between live ranges
- ✅ detects no interference for sequential values
- ✅ handles complex interference patterns
### Capture Buffer Cleanup

- ✅ maintains captured values across calls
- ✅ isolates different capture buffers
- ✅ handles closure returning closure
### Register Spillage

- ✅ handles many live values
- ✅ handles complex expressions with many values
### Register Preservation Across Calls

- ✅ preserves local values across function call
- ✅ preserves values in nested calls
### Optimization Observable Effects

- ✅ produces correct result after vreg reuse
- ✅ preserves value semantics
- ✅ maintains mutation semantics
### Closure Capture Edge Cases

- ✅ captures in deeply nested closures
- ✅ captures the same variable multiple times
- ✅ captures from multiple scopes via lambda
### Capture Buffer Memory Layout

- ✅ stores mixed-type captures
- ✅ captures different sized values
### Performance Characteristics

- ✅ processes many captures efficiently
- ✅ handles array of closures
- ✅ processes filtered captures

