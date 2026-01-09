# Feature #96: Generator Codegen

## Overview

| Property | Value |
|----------|-------|
| **Feature ID** | #96 |
| **Feature Name** | Generator Codegen |
| **Category** | Codegen |
| **Difficulty** | 4 (Hard) |
| **Status** | Complete |
| **Implementation** | Rust |

## Description

Generator state machine code generation. Transforms generator functions with yield statements into resumable state machines with dispatcher entry blocks.

## Specification

[doc/codegen_technical.md](../../codegen_technical.md)

## Implementation

### Files

| File | Purpose |
|------|---------|
| `src/compiler/src/mir/generator.rs` | Generator lowering |
| `src/compiler/src/codegen/cranelift.rs` | Code generation |

## State Machine Structure

| Component | Purpose |
|-----------|---------|
| Dispatcher | Entry block routing by state |
| Resume Blocks | Continuation after each yield |
| State Variable | Tracks current suspension point |
| Frame | Preserved local variables |

## Lowering Process

1. Identify yield points in generator body
2. Split blocks at each yield
3. Create dispatcher with state-based jumps
4. Generate resume blocks for continuations
5. Compute liveness for frame allocation

## Testing

### Test Files

| Test File | Description |
|-----------|-------------|
| `simple/std_lib/test/features/codegen/generator_codegen_spec.spl` | BDD spec (12 tests) |

## Dependencies

- Depends on: #42, #5
- Required by: None

## Notes

Generators are lowered to state machines with dispatcher + resume blocks. Liveness analysis preserves values across suspension points.
