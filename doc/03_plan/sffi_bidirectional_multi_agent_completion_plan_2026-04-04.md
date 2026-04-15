# SFFI Bidirectional Interop Multi-Agent Completion Plan

**Date:** 2026-04-04  
**Status:** Draft  
**Scope:** Complete bidirectional C/C++ SFFI so it moves from “substantial design plus implemented core slice” to a fully supported interop feature.

## 1. Goal

Complete bidirectional interop in both directions:
- Simple -> C/C++ export
- C/C++ -> Simple import and callback/use

The feature should end as:
- a documented, deterministic, proof-backed interop system
- not just a wrapper generator plus partial examples

## 2. Completion Criteria

The feature is complete when:

1. Direction A and Direction B are both explicitly supported.
2. ABI, layout, ownership, and error semantics are documented and enforced.
3. Header/wrapper generation is authoritative, not demo-only.
4. Runtime registration/loading works in supported execution modes.
5. Layout verification is generated and tested.
6. Cross-language round-trip examples pass.
7. README/docs advertise a bounded, proven interop surface rather than “C/C++ complete”.

## 3. Workstreams

### Agent 1: Interop Contract and Support Matrix

Ownership:
- one source-of-truth support contract

Tasks:
- define the supported interop subset:
  - class export rules
  - function export rules
  - import/registration rules
  - callback rules
  - ownership/handle model
  - supported type mappings
- build matrix:
  - feature
  - C support
  - C++ support
  - hosted/runtime support
  - compiled/interpreter support
  - proof status

Acceptance:
- one support matrix drives the rest of the work

### Agent 2: Direction A Export Completion

Ownership:
- Simple -> C/C++

Tasks:
- finish `@export("C")` or equivalent export path
- enforce C-compatible type restrictions
- complete wrapper/header generation for exported classes/functions
- make ownership and handle access explicit

Acceptance:
- exported Simple APIs compile into stable C/C++ callable surfaces

### Agent 3: Direction B Import and Registration Completion

Ownership:
- C/C++ -> Simple

Tasks:
- finish manifest-backed extern registration/import flow
- complete runtime loading/registration for supported modes
- ensure imported classes/functions are callable from Simple with stable semantics

Acceptance:
- one supported runtime path loads and uses foreign classes/functions end to end

### Agent 4: ABI and Layout Verification

Ownership:
- struct/class layout correctness

Tasks:
- finish generated layout verification artifacts
- emit `_Static_assert` / equivalent checks
- verify field offsets, alignment, and repr contracts

Acceptance:
- ABI/layout mismatches fail deterministically at build time where possible

### Agent 5: Ownership, Lifetime, and Error Semantics

Ownership:
- runtime safety model

Tasks:
- define ownership for:
  - borrowed handles
  - owned handles
  - callbacks
  - foreign allocation/deallocation
- define error conversion behavior
- define exception boundary policy for C++

Acceptance:
- no ambiguous lifetime or exception semantics remain in supported paths

### Agent 6: Generator and Tooling Closure

Ownership:
- header/wrapper/tool generation

Tasks:
- make wrapper generation authoritative
- ensure generated code is reproducible
- add deterministic CLI/tooling entrypoints for interop generation

Acceptance:
- users can generate and consume wrappers without manual patching

### Agent 7: Cross-Language Proof Suite

Ownership:
- end-to-end verification

Tasks:
- add round-trip tests:
  - Simple exported to C
  - Simple exported to C++
  - C imported into Simple
  - C++ imported into Simple
  - callback/handle round-trip
- separate:
  - codegen tests
  - ABI/layout tests
  - runtime tests

Acceptance:
- each supported direction has at least one authoritative end-to-end proof

### Agent 8: Public Wording and Scope Control

Ownership:
- docs after proof exists

Tasks:
- update README and audit wording to describe:
  - supported directions
  - supported type subset
  - supported runtime modes
  - known exclusions

Acceptance:
- public wording is derived from the proof matrix

## 4. Execution Order

1. Agent 1 freezes the support contract.
2. Agents 2, 3, 4, and 5 work in parallel.
3. Agent 6 stabilizes generator/tooling surfaces.
4. Agent 7 builds the proof suite.
5. Agent 8 updates docs last.

## 5. Critical Early Decisions

1. Which runtime modes are supported for Direction B?
2. Is C++ exception crossing forbidden or translated?
3. Which type families are first-class in the completion milestone?
4. Is interpreter-mode support required or only compiled-mode?
5. What is the canonical ownership model for exported classes?

## 6. Definition of Done

Bidirectional SFFI is complete when:
- both directions are supported with explicit contracts
- ABI/layout is verified
- generated wrappers are authoritative
- runtime import/export works in supported modes
- end-to-end round-trip tests exist
- docs describe exact supported scope

## 7. Immediate Next Steps

1. Freeze the supported interop subset and runtime modes.
2. Finish layout verification generation.
3. Complete Direction B runtime registration/loading.
4. Build round-trip proof suites for C and C++.
