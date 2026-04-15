# Math Blocks Autograd Completion Plan

**Date:** 2026-04-04  
**Status:** Implemented  
**Scope:** Complete the remaining implementation work for `m{}`, `loss{}`, and `nograd{}` so the feature moves from “implemented and usable, but partial” to a finished runtime-backed feature.

## 1. Current Classification

Math blocks are **partial, not experimental**.

Why they are partial:
- `m{}` syntax, parsing, rendering, and editor tooling are already real
- `loss{}` and `nograd{}` exist as language constructs
- the missing work is the deeper autograd/runtime story, not feature existence

Why they are not experimental:
- the lexer, parser, block registry, HIR resolve, MIR lowering hooks, renderers, Tree-sitter, and editor integrations already exist
- the repo already proves practical use for syntax and rendering
- the incompleteness is specifically in runtime semantics and compiled execution

## 2. Completion Target

The feature is complete when the repo can truthfully state:

> `m{}`, `loss{}`, and `nograd{}` are runtime-backed math blocks with real evaluation, real gradient semantics, deterministic compiled-mode tests, and editor rendering that reflects the same semantics exposed by the language runtime.

This does **not** require a full production deep-learning framework.

It **does** require:
- `m{}` evaluation with a real runtime path
- `loss{}` auto-backward semantics or an equally explicit gradient-trigger contract
- `nograd{}` runtime gradient suppression
- compiled-mode proof for the authoritative execution path
- clear semantics for supported value types and backends

## 3. Current Gaps

Based on the current audit and source state:

### 3.1 `loss{}` autograd semantics are stubbed

Current issue:
- MIR lowering has placeholder comments for backward/autograd integration
- there is no completed runtime call chain that turns `loss{}` into a real gradient-triggering block

Current evidence:
- `src/compiler/50.mir/mir_lowering_ml.spl`
- comments indicating future `rt_backward(...)` style emission

Completion requirement:
- `loss{}` must produce a real, documented runtime effect
- the effect must be tested against a backend that supports gradients

### 3.2 `nograd{}` semantics are not wired through runtime context

Current issue:
- the syntax exists, but there is no finished push/pop no-grad runtime boundary

Current evidence:
- block definitions and lowering exist
- runtime no-grad API exists in the torch backend surface

Completion requirement:
- `nograd{}` must enter and leave a no-grad context in a balanced way
- nested behavior must be defined and tested

### 3.3 Custom block lowering still behaves like a placeholder path

Current issue:
- codegen or lowering currently returns unit placeholders for custom math-mode blocks
- authoritative behavior still leans on interpreter-side or partial runtime assumptions

Completion requirement:
- compiled-mode lowering must produce executable semantics, not only placeholder structure

### 3.4 Test coverage overstates runtime confidence

Current issue:
- many math specs prove parse/load/render but not real execution semantics
- interpreter-mode `it` blocks do not provide authoritative runtime proof

Completion requirement:
- add compiled-mode or backend-backed tests for:
  - `m{}` value evaluation
  - `loss{}` backward effect
  - `nograd{}` suppression effect

### 3.5 Supported backend story is not explicit

Current issue:
- the repo has autograd-related runtime APIs in torch-facing code
- math-block docs do not clearly define which backends actually support gradient semantics

Completion requirement:
- state the supported execution backends for:
  - plain math evaluation
  - gradient-enabled loss evaluation
  - no-grad evaluation

## 4. Final Semantic Contract

### 4.1 `m{}`

Target meaning:
- evaluate a math DSL expression and return its value
- no automatic gradient action

Required support:
- scalar expressions
- supported tensor expressions
- compiled-mode execution for authoritative proof

### 4.2 `loss{}`

Target meaning:
- evaluate a differentiable expression in a gradient-enabled context
- trigger backward automatically or return a runtime object whose gradient action is explicitly defined

Preferred contract:
- automatic backward on block completion when the value is gradient-capable

Allowed fallback contract:
- evaluate as gradient-enabled loss value plus explicit documented backward trigger

But:
- the repo must choose one contract and document it consistently
- README wording must follow the chosen contract, not both

### 4.3 `nograd{}`

Target meaning:
- evaluate the enclosed expression with gradient tracking disabled
- restore the prior grad state when the block exits

Required semantics:
- nesting-safe
- exception/failure safe if the language/runtime has error unwinding in that path
- composable inside and around `loss{}`

## 5. Recommended Runtime Direction

Use the existing torch/autograd runtime as the first authoritative backend.

Reason:
- autograd-related runtime functions already exist
- this closes the real semantic gap with minimal duplication
- the feature can become complete for a scoped backend before broader backend generalization

Primary runtime hooks to align:
- backward
- zero-grad or grad reset where needed for tests
- requires-grad enablement
- no-grad begin/end
- detach or non-grad result handling

Relevant source areas:
- `src/lib/nogc_async_mut/torch/mod.spl`
- `src/lib/nogc_async_mut/torch/backend.spl`
- `src/compiler/50.mir/mir_lowering_ml.spl`

## 6. Implementation Phases

### Phase 1. Define the runtime contract

Goal:
- remove ambiguity about what `loss{}` and `nograd{}` are supposed to do

Tasks:
- document exact runtime semantics for all three blocks
- decide whether `loss{}` auto-runs backward or returns a gradient-capable value plus explicit action
- define supported operand/value categories:
  - scalar-only
  - tensor-only
  - mixed scalar/tensor cases

Artifacts:
- architecture note or detail-design update
- guide update for math/deep-learning behavior

Exit criteria:
- one unambiguous semantics table exists for `m{}`, `loss{}`, `nograd{}`

### Phase 2. Wire `nograd{}` through runtime context

Goal:
- make `nograd{}` a real runtime feature

Tasks:
- add balanced lowering/emission for no-grad begin/end
- ensure restore behavior on nested blocks
- connect to the existing runtime no-grad API

Tests required:
- nested `nograd{}` does not leak state
- `nograd{}` inside `loss{}` suppresses gradient tracking for the enclosed subexpression
- `loss{}` after `nograd{}` resumes normal grad behavior

Exit criteria:
- `nograd{}` changes runtime grad state in compiled-mode proof

### Phase 3. Wire `loss{}` through backward-capable lowering

Goal:
- make `loss{}` a real gradient feature instead of a placeholder

Tasks:
- lower `loss{}` to runtime evaluation plus backward-capable semantics
- connect to the chosen autograd runtime hook
- define result value semantics after backward

Tests required:
- a simple differentiable expression produces non-zero or expected gradients
- repeated loss evaluation behaves predictably with explicit grad reset in the test harness
- unsupported values fail clearly rather than silently succeeding

Exit criteria:
- `loss{}` has one real backend-backed gradient proof

### Phase 4. Remove placeholder compiled behavior

Goal:
- make the compiled path authoritative

Tasks:
- eliminate unit-placeholder behavior for authoritative math block execution paths
- ensure MIR/lowering/codegen represent runtime-backed semantics
- keep interpreter fallback only as a secondary path, not the sole truth

Tests required:
- compiled-mode execution of `m{}`
- compiled-mode execution of `loss{}`
- compiled-mode execution of `nograd{}`

Exit criteria:
- the authoritative math-block specs run in compiled mode and prove runtime behavior

### Phase 5. Build a minimal autograd proof fixture

Goal:
- avoid broad ML complexity while proving semantics cleanly

Recommended fixture shape:
- one small tensor/scalar parameter
- one simple differentiable expression
- one `loss{}` case
- one `nograd{}` case
- one nested-composition case

Suggested proof scenarios:
- `loss{ (w - target)^2 }` updates gradient on `w`
- `nograd{ w * x }` does not record gradient tracking
- `loss{ nograd{ const_part } + grad_part }` only tracks the gradient-enabled part

Exit criteria:
- one compact fixture proves all three semantics against the chosen backend

### Phase 6. Tighten rendering/runtime parity

Goal:
- keep the editor and renderer story aligned with real runtime semantics

Tasks:
- ensure hover text and docs do not imply unsupported derivative features
- decide whether derivative/limit syntax is:
  - supported now
  - rendered only
  - out of scope
- update docs if LaTeX/rendering gaps remain

Exit criteria:
- no doc or editor message claims semantics the runtime does not implement

### Phase 7. Publish supported-backend matrix

Goal:
- make scope explicit instead of leaving it implicit

Matrix should include:
- backend
- `m{}`
- `loss{}`
- `nograd{}`
- compiled proof status
- known limits

Likely first published state:
- pure scalar runtime: `m{}` stable
- torch-backed tensor runtime: `m{}`, `loss{}`, `nograd{}` stable
- other backends: partial or unsupported until proven

## 7. Test Plan

### 7.1 Keep existing syntax/rendering proof

These remain valuable but are not sufficient on their own:
- `test/feature/usage/math_blocks_spec.spl`
- `test/feature/usage/loss_nograd_blocks_spec.spl`
- `test/feature/usage/math_render_spec.spl`
- `test/feature/usage/math_dl_equations_spec.spl`
- `test/feature/usage/math_language_spec.spl`
- `test/feature/usage/implicit_mul_spec.spl`

### 7.2 Add authoritative runtime specs

New required categories:
- compiled `m{}` execution spec
- compiled `loss{}` autograd spec
- compiled `nograd{}` suppression spec
- nested `loss{}` / `nograd{}` interaction spec

### 7.3 Add negative behavior specs

Required:
- unsupported backend or value type fails clearly
- `loss{}` on non-differentiable value path reports a real error
- no-grad state is restored after block exit

### 7.4 Add backend-scoped proof

At least one backend must be fully authoritative:
- recommended first target: torch/autograd path

## 8. Documentation Plan

Update:
- `README.md`
- `doc/report/unique_features.md`
- deep-learning guide docs
- syntax/type/runtime references where math blocks are described

Required wording change after completion:
- move from “autograd runtime wiring not yet connected”
- to a scoped supported statement naming the exact backend(s) that implement `loss{}` and `nograd{}`

## 9. NFR Targets

### Correctness

- gradient semantics must be deterministic for the proof fixture
- no-grad state must restore correctly after nested and sequential evaluation

### Performance

- entering and leaving `nograd{}` should be constant-time runtime state manipulation
- `loss{}` should not add redundant graph traversal beyond the chosen backward contract

### Maintainability

- block semantics should be encoded once in lowering/runtime integration, not duplicated across interpreter/editor/testing paths
- backend-specific autograd logic should stay behind a backend/runtime abstraction

## 10. Recommended Public State After Completion

After Phases 1 through 5 are complete, the repo can describe math blocks as:

- `m{}`: stable runtime-backed math DSL
- `loss{}`: gradient-enabled math block on supported backend(s)
- `nograd{}`: real gradient suppression block on supported backend(s)

At that point the feature moves from:
- implemented and usable, but partial

to:
- implemented with explicit backend-scoped runtime semantics

## 11. Immediate Next Steps

1. Write the exact semantic contract for `loss{}` and `nograd{}`.
2. Implement runtime no-grad begin/end lowering.
3. Implement runtime backward-capable lowering for `loss{}`.
4. Add one compiled-mode backend-backed fixture proving all three blocks.
5. Update docs and README to advertise the now-supported runtime scope precisely.
