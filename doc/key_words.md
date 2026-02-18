# Key words and key points

## Linker Wrapper
Linker wrapper is the native link entry point.

- Input can be `.o`, `.smf`, or `.lsm`.
- For native objects it calls platform linker directly (prefer `mold`, then `lld`, then `ld`/`cc` fallback).
- For `.smf`/`.lsm` it asks ObjectProvider for object bytes.
- If object bytes are missing, it falls back to exported code units and assembles temporary `.o` files through shared `object_emitter`.
- Then it links all resolved objects into final native binary (or self-contained fallback when needed).

## Smf Getter 
SmfGetter locates and reads requested SMF/LSM modules.

- Supports both direct `.smf` files and indexed `.lsm` libraries.
- Returns raw SMF bytes and, when present, embedded object bytes.
- ObjectProvider composes SmfGetter + ObjTaker and adds cache/shared policy:
- SMF byte cache
- object byte cache
- deferred/template symbol materialization through ObjTaker
- exported code-unit fallback for modules without embedded `.o`

## Smf Loader
Loader runtime path:

1. Resolve module through ObjectProvider.
2. Read exported symbols/code.
3. Allocate executable memory.
4. Copy code into memory, then apply RW->RX protection.
5. Register loaded symbols in global symbol table.
6. JIT/ObjTaker path handles deferred/generic symbols on demand.

PIC rule:
- Loader assumes PIC for direct code embedding path.
- Non-PIC modules are rejected for raw-code embedding path.

## Obj mapper (Loader + JIT shared)
Compact research result for sharing SMF loader mapper and JIT mapper.

Current state:
- Loader path already maps bytes with native mmap helpers (`native_alloc_exec_memory`, `native_write_exec_memory`, `native_make_executable`) and tracks symbols in loader table.
- JIT path still has local exec-memory stubs (`alloc_exec_memory`, `write_exec_memory`, `flush_icache`) and a separate `jit_cache` + `symbol_table`.
- This duplicates symbol/address ownership logic and can diverge on lifecycle rules.

Option A: one mapper + mode config
- One `ObjectMapper` type with `mode: Loader | Jit`.
- Pros: minimal type surface.
- Cons: quickly grows conditionals for very different lifecycles (module unload vs symbol replace/re-JIT).

Option B: shared mapper core + thin wrappers (recommended)
- Build one low-level shared core: `SharedExecMapper`.
- Build two policy wrappers:
  - `LoaderMapper` (module ownership, bulk unload by module path)
  - `JitMapper` (symbol ownership, replace-on-recompile, JIT cache binding)
- Pros: shared alloc/write/protect/free path and stats, but lifecycle policy stays clean.
- Cons: small wrapper layer to maintain.

Option C: keep separate mappers, share allocator only
- Lowest refactor risk.
- Still leaves duplicate symbol table + ownership code.

Recommended architecture (Option B):
- Shared core responsibilities:
  - Allocate RW memory, copy bytes, switch to RX, optional icache flush.
  - Track mapped records: `{owner_id, symbol, address, size, generation}`.
  - Support `lookup(symbol)`, `unmap_owner(owner_id)`, `replace(symbol)`, `stats()`.
- Loader wrapper config:
  - `owner_id = module_path`
  - disallow `replace(symbol)` unless hot-reload enabled
  - unload by module path on reload/unload
- JIT wrapper config:
  - `owner_id = "__jit__"` or per-template bucket
  - allow `replace(symbol)` for re-instantiation
  - bind to JIT metadata cache

Security/performance rules:
- Prefer W^X flow: RW allocate -> write -> RX protect (not long-lived RWX).
- Keep icache flush hook in shared core (no-op on x86_64, required on ARM/RISC-V).
- Page-align arena chunks and keep per-owner free lists to reduce mmap churn.

Implementation order:
1. Add `src/compiler_shared/loader/object_mapper.spl` as shared core + config structs.
2. Replace loader local helper (`moduleloader_allocate_exec`) to call shared mapper.
3. Replace JIT exec stubs to call shared mapper; keep JIT compile logic unchanged.
4. Add tests:
   - loader + JIT both map via shared mapper
   - module unload frees owner allocations
   - JIT replace updates symbol address safely

Current gaps found and better way:
- Keep shared core (`SharedExecMapper`) but split policy into two facades:
  - `LoaderMapper`: strict module ownership + unload cleanup
  - `JitMapper`: replace-friendly JIT policy + cache integration
- Avoid global JIT owner for module-linked instantiations:
  - Prefer `owner_id = smf_path` for JIT-compiled symbols originating from a module.
  - This lets module unload/hot-reload reclaim JIT mappings correctly.
- Unload should remove all global symbol-table entries by owner path, not only base exported symbols.
  - Generic/JIT-added symbols can otherwise leave stale entries after memory unmap.
- Keep one source of truth for executable mapping lifecycle:
  - no direct mmap/write/protect calls outside shared mapper
  - no per-component free logic outside mapper API

Decision:
- Best tradeoff is **shared core + Loader/JIT policy wrappers**.
- One mapper with only config flags is workable but tends to grow mode conditionals and weak ownership rules.

## Remote interpreter
Remote interpreter executes same frontend/lowering contract but targets remote memory.

- Generates JIT/native code units.
- Requests exec allocation from remote mapper.
- Uses memory copier bridge (gdb/trace32/etc.) to place bytes remotely.
- Keeps local/remote behavior identical except memory transport backend.

## Remote Smf Loader
Not fully enabled yet.
Design is the same as local loader + remote memory copier backend.

## Memory copyer
Memory copier abstracts byte transfer.

- Local: plain memcpy/no-op abstraction layer.
- Remote baremetal: host -> target transfer via debugger/transport.

## Switchable backend
Simple uses two codegen backends:

- LLVM: release/native-focused builds.
- Cranelift: fast debug/dev path.

Policy:
- Release/native link path should prefer LLVM-compatible object generation.
- Debug/dev can keep Cranelift path.
- SMF metadata/flags must carry enough backend/PIC info so loader/linker can enforce compatibility.

## Fully shared frontend
Frontend must be one shared implementation: Lexer -> Treesitter -> Parser.
No duplicated parser logic in interpreter, loader, or compiler.

### Shared pipeline
1. Lexer creates normalized tokens (same keyword and trivia rules).
2. Treesitter builds stable concrete syntax tree (CST).
3. Parser converts CST to shared AST/HIR entry model.

### Consumers
- Compiler, loader, local interpreter, and remote interpreter all consume the same AST/HIR contract.
- Feature flags only change backend/runtime behavior, not frontend syntax behavior.

### Where specialization is allowed
- After frontend output: lowering, optimization, codegen, loading, execution.
- Runtime-specific validation can be added after parse step, but must not fork grammar rules.

### Rule for logic sharing
- If logic is syntax/structure related, place it in frontend layer.
- If logic is runtime/link/load related, place it after frontend layer.
- This keeps one language behavior and avoids drift between tools.

### Frontend ownership boundary (must share)
- Keyword table, operator precedence/associativity, and token kinds are single source.
- Indentation/newline/trivia normalization is single source.
- CST node shape and AST/HIR entry conversion rules are single source.
- Parse diagnostics format (file/line/column/message) is single source.

### What must NOT happen
- Interpreter must not have private keyword or grammar branch.
- Loader/linker must not parse custom syntax with duplicated rules.
- Tooling parsers can be lightweight scanners, but they must not redefine language grammar.

### Extension workflow for new syntax
1. Add token/keyword once in shared lexer definitions.
2. Add CST handling once in shared Treesitter layer.
3. Add AST/HIR lowering once in shared parser layer.
4. Add/update shared tests for tokenization, CST, parse output, and diagnostics.
5. Only then add backend/runtime behavior (lowering/codegen/interpreter/load).

### Compatibility and rollout rule
- Old and new frontend versions must both parse existing code during migration window.
- If behavior changes, version the feature gate at frontend boundary, not in runtime.
- Remove temporary forks after migration; keep one final shared path.

### Done checklist (frontend sharing complete)
- Same source text produces same AST/HIR for compiler and interpreter path.
- Same syntax error gives same diagnostic message and location in all consumers.
- No duplicated parser grammar file exists for Simple core language.
- CI includes cross-path parse parity tests.

### Minimal flow contract (reference)
```text
source -> shared lexer -> shared treesitter(CST) -> shared parser(AST/HIR)
      -> (compiler lower/codegen) OR (interpreter eval) OR (loader/link path)
```

### Current shared entrypoints (2026-02-18)
- Core frontend runner: `src/core/frontend.spl`
- Full frontend runner: `src/compiler/frontend.spl`
- Core consumers now call shared core frontend entrypoints:
  - `core_frontend_parse_reset`
  - `core_frontend_parse_append`
  - `core_frontend_parse_isolated`
- Full compiler driver now calls `parse_full_frontend` instead of inlining phase 2 logic.


## Boostrap
Bootstrap made by 5 step. 
1. seed: which is written in C++ and can compile Seed Simple Grammar with clang/LLVM.
It impled with C++20 Clang-20.
2. core: Pure simple implementation of simple. It can compile core grammar simple code.
  2-1. core1: it is compiled by seed.
  2-2. core2: it is compiled by core1
It impled with seed simple grammar.
3. full: It is simple with all feature. It can compile full grammar simple code.
  3-1. full1: it is compiler by core2
  3-2. full2: it is compiled by full1
It impled with core simple grammar.
Development is cmake/ninja based.

## Deployment Coverage check
"@deplyment_coverage" is tagged testcase.
It run 2 times.
1. all selected deployment coverage testcases are run first.
when it run callback coverage verifier to runner.
actually it is logged as deployment coverage test loading step.
2. when all none deployment coverage test are ran, it run callback coverage verifier.
it will be showed deployment coverage test running step.
will result by coverage verifier.
Test runner to check file coverage which deployment coverage testcase monitoring to gen coverage on different directories.
before to go 2. step, make link files to overall coverage directory and make each depoyment coverage tests directoy and make link on there.
It can specify coverage listen target by file(however it not specify filename self but module path), and threashold by file or class.
```simple
# @deplyment_coverage
describe "Parser deplyomeent coverage":
  it "should cover LLVMBackend":
    val parser_test = test_group([test.parser.*])
    parser_test.check_coverage(core.parser.llvm_backend.FILE, 50/*branch coverage*/) # it make coverage check callback and register llvm_backe.spl to generate coverage.
  it "should cover CranliftBackend codegen class":
    val cranlift_backend_test = test_group([test.parser.cranlift_backend.*])
    cranlift_backend_test.check_coverage(core.parser.cranlift_backend.FILE, 50, core.parser.cranlift_backend.Codegen.class) # it check Codegen class coverage.
    creanlift_backend_test.check_coverage(.....)


```
