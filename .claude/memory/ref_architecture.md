---
name: Compiler Architecture Reference
description: Compilation pipeline diagrams, MDSOC stages, MIR instructions, backend details, bootstrap chain, desugar passes
type: reference
---

## Default Runtime (Interpreter)
`Source → Desugar (7 passes) → Lexer → Parser → Core Interpreter (tree-walk + JIT)`
Frontend: `compiler/10.frontend/core/` (no treesitter)

## Full Compilation Pipeline
`Source → Desugar → Preprocess → Lexer → TreeSitter outline → Block Resolver → Parser → AST Desugar → Type Check → Mono → HIR → MIR → MIR Opt → Backend → Linker → Loader`

## Source Desugar Passes (`app/desugar/`)
| Pass | Transform |
|------|-----------|
| -2 | `context val` → module var + with_context |
| -1 | `trait Repo: fn find()` → struct with fn fields |
| 0 | `alias fn push = inner.push` → delegation |
| 1 | `impl T: static val X` → `val T__X` |
| 2 | `impl T: static fn f()` → `fn T__f()` |
| 3 | Enum variant factory functions |
| 4 | `T.method()` → `T__method()` rewrite |

## Block Parser System (`compiler/15.blocks/`)
3-phase: lex → treesitter outline → parse_full. Blocks: `m{}`, `sh{}`, `sql{}`, data, loss (ML).

## MDSOC Pipeline Stages
`module_loading → lexing → parsing → desugaring → type_checking → hir_lowering → mir_lowering → optimization → monomorphization → codegen → linking`
Each boundary has typed entity-view adapters (TokenStreamView, AstView, etc.)

## Backend Selection
| Backend | Mode | Key Files |
|---------|------|-----------|
| Cranelift | Debug/JIT | `compiler.spl` |
| LLVM | Release | `llvm_backend.spl` |
| C | Production | `c_backend.spl` |
| Native | Bare-metal | `native/isel_*.spl` |
| WASM | Web | `wasm_backend.spl` |
| CUDA/Vulkan | GPU | `cuda_backend.spl`, `vulkan_backend.spl` |
| VHDL | FPGA | `vhdl_backend.spl` |
| Lean | Verify | `lean_backend.spl` |

## MIR Instruction Categories (50+)
Core(6), Memory(6), Collections(7), Strings(3), Closures(2), Objects(3), Methods(3), Patterns(4), Enums(2), Async(5), Generators(3), Errors(5), Fallback(2), Contracts(2). Each has effect tag.

## AOP (`compiler/90.tools/`)
Pointcuts: NamePattern, Annotation, Module, All. Advice: Before, After, Around. Join points: Execution, Decision, Condition, Error.

## Module Dependency Rules
| Layer | May Access |
|-------|------------|
| `src/app/cli/` | all |
| `src/compiler/` | lib, std |
| `src/lib/` | no deps on compiler/app |

## Lean Verification (`verification/`)
Projects: type_inference, memory_capabilities, SC-DRF, borrow checker, GC safety, async, module resolution.
Commands: `simple gen-lean generate|compare|write`
