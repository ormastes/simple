# Feature Requirement Options: Compiler/Interpreter Optimization + Syntax Sugar

**Date:** 2026-04-29
**Decision required:** choose one option.

## Option A: Performance-First Foundation

**Scope**

- Built-in compile timing report for parser/lowering/typecheck/codegen/link stages.
- Runtime FFI feature gating and lighter startup path.
- Cross-session bytecode/module cache with explicit invalidation rules.
- Adaptive opcode specialization with inline caches as the primary interpreter optimization track.

**Pros**

- Attacks the most likely real bottlenecks first.
- Produces measurement tools needed for later optimization decisions.
- Improves CLI, MCP, and LSP startup/workload behavior.
- Aligns well with current local runtime/startup pain.

**Cons**

- Highest implementation complexity.
- Less immediate visible language ergonomics for end users.
- Requires careful cache invalidation and observability design.

**Effort**

- **Large**

## Option B: Syntax-Sugar and Ergonomics Pack

**Scope**

- Let chains in `if` / `while`.
- `match` guards with pattern-bound names.
- Structured template strings.
- Import attributes / typed imports.
- Lazy iterator helpers desugared to loops.

**Pros**

- Faster to explain and adopt.
- Directly improves compiler/interpreter code readability as well as user ergonomics.
- Lower risk than tiered runtime optimization work.

**Cons**

- Smaller runtime and tooling performance impact.
- Can increase lowering complexity before performance infrastructure is ready.
- Risks creating more sugar that still compiles to suboptimal runtime shapes.

**Effort**

- **Medium**

## Option C: Balanced Backlog

**Scope**

- Built-in compile timing report.
- Runtime FFI feature gating.
- Adaptive specialization spike limited to one hot opcode family.
- Let chains in `if` / `while`.
- `match` guards.
- Structured template strings.

**Pros**

- Mixes measurable performance wins with visible language improvements.
- Lower blast radius than the full performance-first option.
- Creates a practical roadmap for design and implementation sequencing.

**Cons**

- Less transformative than Option A.
- Less focused than Option B.
- Requires disciplined scope control to avoid becoming “everything at once”.

**Effort**

- **Medium-Large**

## Option D: Research-Backlog Only

**Scope**

- No implementation commitment yet.
- Produce a ranked feature-request backlog grouped into:
  - optimization,
  - syntax sugar,
  - tooling/startup,
  - runtime architecture.

**Pros**

- Lowest short-term risk.
- Useful if architecture decisions are still moving quickly.
- Good fit if you want multiple later design/impl tracks.

**Cons**

- No direct product improvement.
- Easy to stall without a follow-up decision.
- Does not force performance measurement targets.

**Effort**

- **Small**
