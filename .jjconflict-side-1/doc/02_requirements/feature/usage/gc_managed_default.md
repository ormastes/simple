# gc managed default
*Source:* `test/feature/usage/gc_managed_default_spec.spl`

## Overview

GC Managed Default Types Tests
Feature: Default garbage collection for managed types
Category: Runtime
Status: In Progress

Tests for garbage collection as the default memory management strategy,
including type inference, collection behavior, and integration with
reference capabilities.

## Feature: GC Managed Default Types

Tests for type inference and default GC management,
    verifying that types default to GC-managed when appropriate.

### Scenario: when type is not explicitly constrained

### Scenario: Default Type Inference

        Tests that types without explicit capability constraints
        default to GC management.

| # | Example | Status |
|---|---------|--------|
| 1 | infers GC type for unqualified reference | pass |
| 2 | creates GC type for struct instantiation | pass |

### Scenario: when inferring container types

### Scenario: Container Type Inference

        Tests that containers default to GC management.

| # | Example | Status |
|---|---------|--------|
| 1 | creates GC-managed list by default | pass |
| 2 | creates GC-managed dict by default | pass |

## Feature: GC Collection Behavior

Tests for garbage collection behavior, including
    when objects are collected and resource cleanup.

### Scenario: when object becomes unreachable

### Scenario: Object Collection

        Tests that unreachable objects are properly collected.

| # | Example | Status |
|---|---------|--------|
| 1 | collects unreachable GC objects | pass |
| 2 | finalizes collected objects | pass |

### Scenario: when memory pressure exists

### Scenario: GC Under Memory Pressure

        Tests garbage collection behavior under resource constraints.

| # | Example | Status |
|---|---------|--------|
| 1 | triggers collection when needed | pass |
| 2 | frees memory from dead objects | pass |

## Feature: GC with Reference Capabilities

Tests for interaction between GC management and reference capabilities,
    including mutable, immutable, and isolated references.

### Scenario: when using mutable GC references

### Scenario: Mutable GC References

        Tests mutable references in GC-managed context.

| # | Example | Status |
|---|---------|--------|
| 1 | allows mutation of GC-managed objects | pass |
| 2 | tracks mutations for write barriers | pass |

### Scenario: when sharing GC references

### Scenario: Reference Sharing

        Tests sharing of GC-managed objects across references.

| # | Example | Status |
|---|---------|--------|
| 1 | allows multiple references to GC object | pass |
| 2 | prevents use-after-free with GC | pass |

## Feature: GC Performance Characteristics

Tests for garbage collection performance,
    including collection pause times and memory overhead.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | maintains reasonable pause times | pass |
| 2 | avoids collecting live objects | pass |
| 3 | efficiently handles large object graphs | pass |


