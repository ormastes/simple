# Simple Unique Features Audit

**Date:** 2026-03-31  
**Scope:** Audit of distinctive Simple features requested for README cleanup and repo documentation.  
**Method:** local source/doc inspection plus parallel sub-agent verification across testing, runtime/backend, and language/tooling areas.

## Summary

Simple's strongest differentiators are not just syntax features. The repo's unusual value is that language, compiler, interpreter, loader, testing stack, doc generation, project metadata, and baremetal-oriented execution all live in one self-hosted system.

The most defensible claims are:

- staged self-hosted compiler/interpreter/loader architecture
- compiler-integrated verification stack: SSpec, SDoctest, coverage, traceability, generated specs
- MDSOC as a real architectural layer
- parser-friendly macros with validation and hygiene
- Tree-sitter tooling integration
- SDN-backed project/test/todo/dashboard databases
- baremetal build and test plumbing
- mmap-backed SMF/module loader support
- primitive-public-API linting
- statistics/doc-coverage/tooling support

Several requested items are real but only partial, experimental, or host-dependent. Those should be documented with qualifiers rather than marketed as complete.

## Completeness Matrix

| Feature | Status | Notes |
|---|---|---|
| SSpec | Implemented | Real framework with broad repo coverage |
| SDoctest | Implemented | Runner, extraction, docgen, result DB |
| Coverage | Implemented | CLI support plus compiler/runtime support |
| Traceability | Implemented | Tooling-level source/spec mapping |
| Generated spec docs | Implemented | `sspec-docgen` plus generated docs under `doc/06_spec/` |
| Lean generation for verification | Partial | Real generation/proof artifacts, incomplete integration |
| MDSOC | Implemented | Architectural concept plus source/config artifacts |
| Parser-friendly macros | Implemented | Validation and hygiene are real |
| Tree-sitter | Implemented with debt | Strong tooling support, some TODO/skip debt remains |
| SDN project DB / test DB / todo DB | Implemented | Strong repo-wide pattern |
| Math blocks `m{}` | Implemented | Real syntax/tests |
| `loss{}` / `nograd{}` blocks | Implemented with scope limits | Parsing/evaluation/rendering verified; broader DL story still evolving |
| Primitive type warning on public API | Implemented | `primitive_api` lint |
| Borrow-checking infrastructure | Implemented | Compiler borrow/lifetime modules exist |
| Watch mode / auto-build | Implemented | Polling watcher plus daemon/build support |
| mmap file loading | Implemented | SMF/native loader support exists |
| Interpreter / loader / compiler support | Implemented | Staged architecture is real |
| Baremetal-friendly runtime/build | Implemented | Real build/test plumbing |
| Remote baremetal test runner | Implemented with host-dependent lanes | Plumbing exists, CH32 composite execution is real, but repo-wide end-to-end status still depends on host tools and boards |
| Test session sharing | Implemented | Test DB/run DB support |
| UI sharing with TUI and GUI | Partial | Shared UI testing surface is real; one unified UI layer is not proven |
| AOP | Partial | Real compiler/runtime surface, but some stubs remain |
| C/C++ bidirectional interface | Partial | Strong SFFI stack; bidirectional completeness not proven |
| LLVM backend | Partial but real | Real backend and LLVM-oriented flows; still tool-dependent and not uniformly complete |
| VHDL backend | Experimental | Concrete codegen surface exists, but should not be presented as complete |
| GC and no-GC mode support | Partial but substantial | Multiple runtime families exist, completeness varies by path |
| Language statistics | Implemented | CLI/tooling support exists |
| Coverage thresholds against dummy implementations | Partial but meaningful | Stub lint and coverage enforcement exist; not a universal proof against every weak implementation |
| Language-level mock policy in system tests | Implemented with scope | Executor-path proof now covers system-test bans plus unit-test override behavior |
| Declarative argparser integrated into language | Partial but real | `cli Name:` parser, interpreter evaluation, and backend codegen exist; this is not yet the uniform CLI path for every app |
| Semantic wrapper / unit-type patterns | Implemented | `unit`-based semantic types are documented and used across stdlib-facing APIs |
| VS Code / Neovim math rendering | Implemented with qualifiers | Query/LSP hover, VS Code inline decoration, preview panel, and Neovim conceal are real; broader polished editor UX is still evolving |

## Evidence By Area

### 1. Verification-Native Toolchain

Implemented:

- SSpec framework: `src/lib/nogc_sync_mut/sspec.spl`
- Test usage/docs: `test/README.md`
- SDoctest runner: `src/lib/nogc_sync_mut/test_runner/sdoctest/runner.spl`
- SDoctest docgen: `src/lib/nogc_sync_mut/test_runner/sdoctest/doc_gen.spl`
- Coverage entrypoints: `src/app/coverage/main.spl`
- Traceability tooling: `src/app/traceability/main.spl`
- Generated spec docs: `src/app/sspec_docgen/main.spl`

Important distinction:

- this is stronger than “the project has tests”
- the repo embeds a testing and documentation pipeline into the language/toolchain itself

### 2. Self-Hosted Staged Architecture

Implemented:

- frontend: `src/compiler/10.frontend/`
- types: `src/compiler/30.types/`
- borrow checking: `src/compiler/55.borrow/`
- backend: `src/compiler/70.backend/`
- driver: `src/compiler/80.driver/`
- interpreter: `src/compiler/95.interp/`
- loader: `src/compiler/99.loader/`

Distinctive value:

- the repo exposes compiler, interpreter, loader, and toolchain stages directly as source-level architecture rather than hiding them behind one opaque binary

### 3. MDSOC

Implemented:

- architecture docs: `doc/04_architecture/README.md`
- manifest/type surface: `src/compiler/85.mdsoc/types/mdsoc_manifest.spl`
- repo config artifact: `src/os/capsule.sdn`

Distinctive value:

- MDSOC is one of the clearest “this is not a generic hobby language” differentiators in the repo

### 4. Macros and Tooling Friendliness

Implemented:

- macro definitions: `src/compiler/30.types/macro_def.spl`
- macro expansion: `src/compiler/30.types/macro_expander.spl`
- macro validation: `src/compiler/35.semantics/macro_validation.spl`
- macro hygiene: `src/compiler/35.semantics/macro_check/hygiene.spl`

Distinctive value:

- Simple is not only claiming macros; it is explicitly aiming for parser-friendly, validated, hygienic macros

### 5. Tree-Sitter and Editor Tooling

Implemented with debt:

- Tree-sitter parser/tooling: `src/compiler/10.frontend/treesitter.spl`
- outline tooling: `src/compiler/10.frontend/treesitter/outline.spl`
- query files: `src/compiler/10.frontend/parser/treesitter/queries/`
- Neovim plugin artifact: `src/app/nvim_plugin/lua/simple/treesitter.lua`
- guide: `doc/07_guide/tooling/treesitter.md`

Qualification:

- good evidence for tooling integration
- not enough evidence for a polished “editor rendering for all special DSL blocks” claim

### 6. SDN-Backed Textual Databases

Implemented:

- unified DB: `src/compiler_rust/driver/src/unified_db.rs`
- test DB: `src/compiler_rust/driver/src/test_db.rs`
- todo DB: `src/compiler_rust/driver/src/todo_db.rs`
- data artifacts: `doc/test/test_db.sdn`, `doc/todo/todo_db.sdn`

Recommended wording:

- “SDN-backed project/test/task databases”

Avoid:

- presenting this as one polished end-user “project DB product” unless the UX is documented as such

### 7. Baremetal and Remote Execution

Implemented:

- baremetal build path: `src/compiler/80.driver/build/baremetal.spl`
- LLVM IR path: `src/compiler/80.driver/build/compile_to_llvm.spl`
- baremetal tests/specs: `test/system/baremetal_test_runner_spec.spl`, `test/feature/baremetal/`
- remote baremetal runtime spec: `test/feature/app/remote_baremetal/remote_baremetal_runtime_spec.spl`
- remote baremetal library spec: `test/feature/app/remote_baremetal/remote_baremetal_library_spec.spl`

Qualification:

- remote baremetal support is real enough to document as a differentiator
- stable RV32 ELF/shared-workload proof is green
- CH32 composite-runner execution is real through the `wlink` adapter path
- docs should still avoid claiming universally green full hardware execution across every host and board

### 8. Loader, mmap, and Executable Memory

Implemented:

- module loader: `src/compiler/99.loader/loader/module_loader.spl`
- mmap support: `src/compiler/99.loader/loader/smf_mmap_native.spl`

Qualification:

- loader/JIT now has a real shared-cache and executable-mapping path through `module_loader.spl` and `jit_instantiator.spl`
- docs should still avoid claiming universal end-to-end coverage across every runtime/backend combination; the verified evidence here is targeted compiler loader/linker coverage

### 9. Backends

Real:

- LLVM backend: `src/compiler/70.backend/backend/llvm_backend.spl`
- VHDL backend surface: `src/compiler/70.backend/backend/vhdl_backend.spl`

Qualification:

- LLVM is real but still dependent on external LLVM tools in some flows
- VHDL should be labeled experimental, not complete

### 10. Safety / API Hygiene / Borrowing

Implemented:

- primitive API lint: `src/compiler/35.semantics/lint/primitive_api.spl`
- borrow graph: `src/compiler/55.borrow/borrow_check/borrow_graph.spl`
- lifetime support: `src/compiler/55.borrow/borrow_check/lifetime.spl`
- semantic wrapper / unit-type guidance: `doc/07_guide/language/type_system.md`
- semantic wrapper rollout evidence: `doc/09_report/misc/primitive_api_project_closure.md`
- cross-module wrapper proof: `test/integration/app/unit_wrapper_module_boundary_spec.spl`

Qualification:

- a completed polished borrowing user guide was not verified
- “limited scope borrowing and its guide document and generated spec” is too strong as a README claim
- the repo evidence is for `unit`-style semantic wrappers, not built-in primitive redefinition

### 10a. Mock Policy Enforcement

Implemented with scope:

- executor integration proof: `test/integration/spec/mock_policy_execution_spec.spl`
- runtime policy hooks: `src/compiler_rust/lib/std/src/spec/mock.spl`
- executor wiring: `src/compiler_rust/lib/std/src/spec/runner/executor.spl`
- lower-level enforcement/unit coverage: `test/unit/lib/nogc_sync_mut/mock_policy_spec.spl`

Qualification:

- this is a scoped SSpec/system-test feature, not a universal language-wide impossibility result
- the safe claim is that system-test execution bans mocks by default while unit-test paths can opt back in

### 10b. Math Block Editor Rendering

Implemented with qualifiers:

- query/LSP hover surface: `src/app/cli/query_visibility.spl`
- query hover regression: `test/integration/app/query_visibility_surfaces_spec.spl`
- VS Code inline decoration/hover/preview: `src/app/vscode_extension/src/math/`
- Neovim conceal/preview: `src/app/nvim_plugin/lua/simple/math.lua`
- rendering core: `src/lib/common/math_repr.spl`

Qualification:

- the editor story is now real enough to advertise with scope
- avoid calling it a fully polished unified editor experience; keep the wording specific to hover, decorations, preview, and Neovim conceal

### 11. UI Sharing and UI Testing

Implemented in part:

- shared UI test client: `src/lib/nogc_sync_mut/ui_test/client.spl`
- testing guide explicitly describes shared test API across web backend and TUI web proxy: `doc/07_guide/testing/testing.md`

Qualification:

- this is enough to claim shared UI testing surface
- this is not enough to claim a fully unified TUI/GUI application layer

## Requested Claims That Need Downgrading

These should not be advertised as complete in README:

- Lean verification as a finished verification pipeline
- remote interpreter / remote baremetal end-to-end execution on all lanes
- VHDL backend support as production-ready
- C/C++ bidirectional interop as complete
- custom primitive redefinition

## Recommended README Positioning

Use Simple's differentiators in three tiers:

1. Strong differentiators
- self-hosted staged compiler/interpreter/loader
- verification-native toolchain
- MDSOC
- parser-friendly macros
- SDN-backed project databases
- baremetal-oriented build/test plumbing

2. Strong but scoped
- Tree-sitter integration
- math/loss/nograd blocks
- system-test mock policy
- semantic wrapper / unit-type patterns
- UI test sharing between web and TUI-web surfaces
- primitive API linting
- mmap-backed loader support

3. Experimental / partial
- AOP
- remote baremetal end-to-end hardware flows
- LLVM/VHDL backend completeness
- C/C++ bidirectional interop
- full GC/no-GC story
- Lean verification integration

## Spawn-Agent Check

Parallel sub-agents were used for this audit and returned useful, non-duplicative findings in three clusters:

- verification/testing
- runtime/backend/platform
- language/tooling/architecture

For this task, spawn-agent support worked and did not require fixes.
