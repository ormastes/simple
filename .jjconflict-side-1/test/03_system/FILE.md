# test/03_system/ Manifest

System-level tests organized by domain category.

## Allowed Entries

| Entry | Description |
|---|---|
| `acceptance/` | Acceptance tests (25 staged scenarios) |
| `app/` | Application-level system tests (browser, compiler, editor, ide, mcp) |
| `compiler/` | Compiler system tests (comprehensive, module_import, runtime, sffi) |
| `core/` | Core behavior tests (edge_case, error_path, regression, resilience) |
| `e2e/` | End-to-end tests (integration, functional, adapter) |
| `engine/` | Game/physics engine tests (2d, 3d, game2d, physics) |
| `feature/` | Language feature tests (857+ spec files) |
| `generated/` | Auto-generated test files |
| `gui/` | GUI/editor/UI tests (editor, compositor, wm_compare, reftest) |
| `hardware/` | Hardware tests (rv32imac, vhdl, t32, fpga, drivers) |
| `helpers/` | Shared test helpers |
| `infrastructure/` | Build/CI/deploy tests (batch, smoke, sanity, coverage) |
| `interpreter/` | Interpreter-specific tests |
| `os/` | OS tests (kernel, qemu, network, shell, ssh, storage, simpleos) |
| `quality/` | Code quality tests (coupling, duplication, performance) |
| `security/` | Security tests (aop, crypto, ed25519, x25519) |
| `stdlib/` | Standard library tests (database, math, dynload, async) |
| `stress/` | Stress tests (25 numbered scenarios) |
| `tools/` | Developer tool tests (lint, lsp, mcp, dap, repl, jupyter, watcher) |
| `verification/` | Formal verification system tests |
| `FILE.md` | This manifest |
