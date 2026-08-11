# Feature Request List: Compiler/Interpreter Optimization + Syntax Sugar

**Date:** 2026-04-29
**Status:** Research-derived backlog, not final selected requirements
**Sources:** Local repo research plus external Rust, Python, and JavaScript research

## Priority 1: Optimization Foundation

### FR-001 Adaptive opcode specialization with inline caches

Add adaptive interpreter specialization for selected hot opcode families, backed by inline caches and explicit de-specialization paths.

**Why**

- Highest-confidence interpreter optimization across dynamic language implementations.
- Matches CPython quickening/specialization and JS engine IC-heavy designs.
- Creates a path toward future tiered execution without requiring immediate full JIT maturity.

**Expected impact**

- Better steady-state interpreter throughput.
- Better understanding of hot-path shapes through counters and diagnostics.

**Effort**

- Large

### FR-002 Cross-session bytecode or module cache

Add a persistent cache for compiled bytecode or equivalent module artifacts with strict invalidation based on source, config, and compiler/runtime version.

**Why**

- Strong startup win for repeated CLI, MCP, and LSP workloads.
- Repeated short-lived processes benefit more from caching than from deeper optimizer work alone.

**Expected impact**

- Faster warm startup.
- Lower repeated compilation cost in tooling-heavy workflows.

**Effort**

- Medium

### FR-003 Compiler timing and hot-stage reporting

Add first-class timing reports for parser, lowering, type inference/checking, MIR/backend generation, linking, and cache hits or misses.

**Why**

- Needed before making broader optimization claims.
- Rust/Cargo timing visibility is a proven low-risk optimization enabler.

**Expected impact**

- Better prioritization of optimization work.
- Easier regression detection for startup and throughput.

**Effort**

- Medium

### FR-004 Runtime optional-subsystem feature gating

Feature-gate optional runtime subsystems such as HTTP, TLS, regex, and hashing extensions so they are not always pulled into startup and linked binaries.

**Why**

- This is already a visible local repo issue.
- Improves startup path, binary size, and deployment flexibility.

**Expected impact**

- Smaller linked binaries.
- Lower startup overhead for programs that do not use optional FFIs.

**Effort**

- Medium

## Priority 2: Mid-Tier Runtime Architecture

### FR-005 Tier-2 micro-op or CFG/SSA middle IR

Introduce a mid-tier IR between generic interpreter execution and heavyweight native optimization, designed for specialization, inlining, and deopt-friendly transformations.

**Why**

- Python and JS engines both benefit from a staged execution pipeline.
- Avoids jumping directly from generic execution to expensive optimization.

**Expected impact**

- Better path for hot code optimization.
- Cleaner implementation surface for later JIT or advanced specialization work.

**Effort**

- Large

### FR-006 Shared instruction metadata or instruction DSL

Unify interpreter instruction definitions, optimization metadata, and tooling-visible opcode information under one source of truth.

**Why**

- Reduces drift across runtime, optimizer, diagnostics, and future code generators.
- Inspired by CPython’s shared instruction-definition direction.

**Expected impact**

- Lower maintenance cost.
- Easier rollout of specialized instructions and diagnostics.

**Effort**

- Large

## Priority 3: Compiler/Language Ergonomics

### FR-007 Let chains in `if` and `while`

Add compact chained pattern-binding conditions for `if` and `while`.

**Why**

- Directly improves compiler-pass, lowering, and interpreter code readability.
- Good payoff for modest syntax complexity.

**Expected impact**

- Less nested control flow in compiler and runtime code.
- Better readability for pattern-heavy logic.

**Effort**

- Small to Medium

### FR-008 `match` guards with pattern-bound names

Add guard expressions on `match` arms that can use names bound by the matched pattern.

**Why**

- Useful for AST/IR rewrites and interpreter dispatch refinement.
- Strong ergonomic precedent in Rust and Python pattern systems.

**Expected impact**

- Cleaner branching logic.
- Fewer nested post-match conditionals.

**Effort**

- Medium

### FR-009 Structured template strings

Extend current interpolation with structured template-string support that preserves segments and interpolated values until rendering time.

**Why**

- Better fit for SQL, HTML, logging, command construction, and future DSL work.
- Stronger than plain interpolation for safe composition.

**Expected impact**

- Safer embedded DSL construction.
- Better tooling hooks for structured rendering and validation.

**Effort**

- Medium

### FR-010 Import attributes or typed import metadata

Add import-site metadata for loader-visible typed imports such as JSON or future asset classes.

**Why**

- Cleaner than ad hoc loader behavior.
- Good foundation for non-code module support.

**Expected impact**

- More explicit module loading contracts.
- Easier future extension of module types.

**Effort**

- Medium

### FR-011 Lazy iterator helpers desugared to loops

Add a focused lazy-iterator helper surface with predictable lowering to loops or existing iterator machinery.

**Why**

- High ergonomic value without forcing eager allocation.
- Good match for JS iterator-helper lessons.

**Expected impact**

- Cleaner sequence-processing code.
- Better control over allocation behavior than eager helpers.

**Effort**

- Medium

## Priority 4: Advanced Specialization

### FR-012 Call-site specialization and trial inlining

Specialize hot call sites and allow limited trial inlining where profiling or static evidence justifies it.

**Why**

- Important bridge between interpreter specialization and full optimizing compilation.
- Can improve higher-order and closure-heavy code.

**Expected impact**

- Better performance on hot call paths.
- More optimization exposure for downstream passes.

**Effort**

- Large

### FR-013 CPU-feature-gated fast paths

Allow runtime or build-selected CPU-feature-specific fast paths for targeted primitives.

**Why**

- Useful for parsing, hashing, text processing, and SIMD-friendly runtime helpers.
- Good fit for native backend/runtime optimization work.

**Expected impact**

- Faster selected primitives on supported hardware.

**Effort**

- Medium

## Ranking Guidance

If the goal is **practical near-term value**, start with:

1. `FR-003` Compiler timing and hot-stage reporting
2. `FR-004` Runtime optional-subsystem feature gating
3. `FR-002` Cross-session bytecode or module cache
4. `FR-007` Let chains in `if` and `while`
5. `FR-008` `match` guards with pattern-bound names

If the goal is **maximum long-term performance leverage**, start with:

1. `FR-001` Adaptive opcode specialization with inline caches
2. `FR-005` Tier-2 micro-op or CFG/SSA middle IR
3. `FR-006` Shared instruction metadata or instruction DSL
4. `FR-012` Call-site specialization and trial inlining

## Non-Selection Note

This file is a feature-request backlog only. It does not replace the required user selection step for final feature and NFR requirements.
