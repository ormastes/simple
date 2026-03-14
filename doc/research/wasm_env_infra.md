# WASM Backend + Environment Infrastructure — Research

**Feature ID:** WASM-ENV-INFRA
**Date:** 2026-03-14
**Cross-ref:** `doc/requirement/wasm_env_infra.md`

---

## 1. WASM Backend — Current State

### Two Existing Paths

| Path | Files | Status | Use Case |
|------|-------|--------|----------|
| **Standalone WAT** | `wasm_backend.spl`, `wat_codegen.spl`, `wasm_memory.spl`, `wasm_control_flow.spl` | 95% — adapter stub blocks integration | Debug/fast compile |
| **LLVM → WASM** | `llvm_backend.spl`, `mir_to_llvm.spl` + `wasm-ld` | Complete — targets wasm32-wasi/wasm64-wasi | Release/optimized |

### Standalone WAT Path (Gap Analysis)

**Complete:**
- `MirToWat` translator (543 lines) — all MIR instruction types
- `WatBuilder` — WAT text emission API (module, functions, imports, exports)
- `WasmMemoryManager` — linear memory, string table, bump allocator (4MB initial/256MB max)
- `WasmTypeMapper` — 23 methods covering all MIR types
- `WasmControlFlow` — Relooper-based block/loop/if structuring
- `WasmBackend` — browser/WASI/minimal target orchestration, JS glue generation

**Single Gap:** `wasm_codegen_adapter.spl:30` — `compile_module()` returns stub `"(module)"` instead of calling `MirToWat.translate_module()`. This is ~5 lines of wiring code.

### LLVM → WASM Path

**Complete:**
- `llvm_target.spl` generates `wasm32-wasi` / `wasm64-wasi` triples
- `llvm_backend_tools.spl` has `compile_ir_to_wasm()` function
- `wasm_linker.spl` wraps `wasm-ld` with browser/WASI/minimal linking modes
- Stack-first memory layout, WASI sysroot support

**Requirements:** LLVM 16+ (`llc`), `wasm-ld`, optionally `wasm-opt`

### Backend Selector Integration

`backend_helpers.spl` already routes:
- WebAssembly → Wasm backend (standalone)
- But does NOT differentiate debug vs release for WASM targets

**Recommendation:** Follow the existing pattern (Cranelift=debug, LLVM=release):
- WASM debug → standalone WAT (fast compile)
- WASM release → LLVM → wasm-ld (optimized output)

### Test Coverage

- 36 WASM tests in `src/compiler_rust/driver/tests/wasm_tests.rs` (all passing)
- Feature spec: `doc/spec/feature/wasm_compile_spec.md` (36/36 passing)
- No end-to-end test from `.spl` → `.wasm` → runtime execution

---

## 2. Container Infrastructure — Current State

### Existing Modules (Fragmented)

| Module | Location | Purpose | API Style |
|--------|----------|---------|-----------|
| Docker Runner | `src/app/test/docker_runner.spl` | CLI tool (build/run/shell/clean) | Command-based |
| QEMU Manager | `src/app/vm/qemu_manager.spl` | VM lifecycle (start/stop/exec/copy) | Function-based |
| QEMU Broker | `src/app/test_daemon/qemu_broker.spl` | Session pooling with QMP snapshots | Struct-based |
| QEMU Builder | `src/compiler/80.driver/build/qemu_builder.spl` | Custom QEMU build (string interning) | Build tool |
| Execution Strategy | `src/app/test_runner_new/execution_strategy.spl` | Test mode selection | Enum+struct |
| Sequential Container | `src/lib/nogc_sync_mut/test_runner/sequential_container.spl` | One-at-a-time container runs | Runner |
| Container Test | `src/app/test/container_test.spl` | Local container helper | STUB (broken) |
| Container Loader | `src/compiler/99.loader/settlement/container.spl` | Module loading in containers | Internal |
| Docker Setup | `src/compiler/90.tools/verify/docker_setup.spl` | Docker env verification | Setup |
| FreeBSD QEMU | `src/app/test/freebsd_qemu_setup.spl` | FreeBSD VM bootstrap | Setup script |

### Docker Compose Configs

| File | Services | Purpose |
|------|----------|---------|
| `config/docker-compose.yml` | unit/integration/system/dev-shell/watch | Development |
| `config/docker-compose.test.yml` | test-isolation, test-full | CI testing |
| `config/t32/trace32_x11_container.compose.yml` | trace32-stm | HW debugger |

### Dockerfiles

| File | Base | Purpose |
|------|------|---------|
| `tools/docker/Dockerfile.test-isolation` | Ubuntu 24.04 | Minimal secure test env |
| `tools/docker/Dockerfile.jupyter-test` | Ubuntu 24.04 | Jupyter kernel testing |

### SDN Configs (Existing)

- `resources/boards/qemu_x86.sdn` — QEMU x86 board definition
- No unified environment config format exists yet

### Key Findings

1. **No unified API** — each module has its own lifecycle interface
2. **No SDN-based config** — container/QEMU configs are hardcoded or in Docker Compose YAML
3. **Runtime detection works** — docker/podman auto-detection exists in `docker_runner.spl` and `trace32_x11_container.shs`
4. **QEMU Broker is sophisticated** — session pooling, QMP snapshots, hash-based reuse
5. **Execution Strategy has the right enum** — `native`, `process`, `safe`, `container`, `container-sequential` but no `qemu` or `hw_debugger` variants

---

## 3. Test Environment System — Current State

### Existing Annotations

| Annotation | Location | Purpose |
|-----------|----------|---------|
| `# @mode: interpreter, native` | File-level | Restrict to specific execution modes |
| `# @skip_mode: interpreter` | File-level | Skip in specific modes |
| `# @platform: baremetal(arm32)` | File-level | Platform tag |
| `# @pending` | File-level | Mark as pending |
| `# @di_test` | File-level | Allow DI in system tests |
| `slow_it(name, block)` | Test-level | Slow test marker |
| `skip(reason)` | Test-level | Skip with reason |

### Decorator System (Runtime)

`decorators.spl` provides:
- `skip(platforms, runtimes, profiles, architectures, features, reason)` — multi-criteria skip
- `only_on(...)` — positive filter
- `skip_if(condition_fn, reason)` — dynamic condition
- Convenience: `only_on_linux()`, `only_on_baremetal()`, `skip_on_interpreter()`, etc.

### Environment Detection (11 categories)

`env_detect.spl` detects: platform, runtime mode, build profile, architecture, features, hardware capabilities, dependencies, env vars, filesystem, network, compiler version.

### Gap: No `@environment()` Annotation

- Current system routes tests by **mode** (interpreter/native/smf) and **platform** (baremetal/arch)
- No way to say "this test needs a Docker container" or "this test needs a QEMU VM"
- `ExecutionStrategy` has container modes but they're selected by the runner, not declared by tests
- The `Composite(spec)` mode in `TestExecutionMode` could be extended for this

### Recommended Approach

Extend the existing annotation system rather than replacing it:
```
# @environment(docker-isolation)     # named environment from config
# @environment(container)            # generic: any container
# @environment(qemu:freebsd)         # QEMU with specific config
# @environment(hw:trace32)           # hardware debugger
```

This maps to `TestExecutionMode.Composite(spec)` with the spec being the environment name.

---

## 4. VSCode Extension — Current State

### Architecture

| Layer | Language | Lines | Status |
|-------|----------|-------|--------|
| Extension host | TypeScript | ~537 | Complete |
| LSP server | Simple | ~2,364 | Complete |
| DAP server | Simple | manifests | Protocol ready |
| WASM bridge | TypeScript | ~325 | Complete |
| Neovim plugin | Lua | ~200+ | Complete |
| E2E tests | TypeScript | ~1,587 | Complete (need display) |

### Testing Problem

- Tests use `@vscode/test-electron` — requires Electron → requires display
- Headless machine cannot run tests
- Solution: Docker container with Xvfb (virtual framebuffer)

### Migration Opportunities

| Component | Migrate to Simple? | Rationale |
|-----------|-------------------|-----------|
| Extension host (`extension.ts`) | Partial — keep TS bridge | VSCode API requires TypeScript/JavaScript |
| WASM bridge (`wasmLspBridge.ts`) | No | WASI API is JavaScript-only in VSCode |
| AI features (`ai/*.ts`) | No | Uses VSCode LanguageModel API |
| Math rendering (`math/*.ts`) | Possible | Could compile to WASM |
| Test utilities (`test/helpers/`) | Possible | Could use SSpec via WASM |
| LSP server | Already Simple | 100% Simple |
| DAP server | Already Simple | 100% Simple |

**Realistic migration scope:** Math rendering and test helpers could be compiled to WASM and called from TypeScript. The extension host must remain TypeScript.

---

## 5. Commonization Opportunities

### Container/QEMU → Unified Environment API

```
Current (fragmented):
  docker_runner.spl    → CLI commands (build/run/clean)
  qemu_manager.spl     → Functions (vm_start/vm_stop/vm_exec)
  qemu_broker.spl      → Session pool (QMP snapshots)
  execution_strategy.spl → Mode enum
  sequential_container.spl → Sequential runner

Proposed (unified):
  lib/env/
    environment.spl      → Environment trait + factory
    container.spl        → Container implementation (wraps docker/podman)
    qemu.spl             → QEMU implementation (wraps qemu_manager)
    hw_debugger.spl      → HW debugger implementation (wraps T32)
    remote.spl           → Remote SSH implementation
    config.spl           → SDN config loader
    pool.spl             → Environment pooling (wraps qemu_broker pattern)
    registry.spl         → Named environment registry
```

### Test Runner Integration

```
Current:
  execution_strategy.spl decides mode → runs directly

Proposed:
  @environment(name) annotation
    → test_runner reads annotation
    → looks up environment config from registry
    → environment.start()
    → environment.exec("bin/simple test this_file.spl")
    → environment.stop() (or return to pool)
```

### Config Consolidation

```
Current:
  config/docker-compose.yml          (YAML - Docker specific)
  config/docker-compose.test.yml     (YAML - Docker specific)
  config/t32/trace32_x11_container.compose.yml (YAML)
  resources/boards/qemu_x86.sdn     (SDN - QEMU board only)

Proposed:
  config/environments/
    docker-isolation.sdn       (unified SDN)
    docker-full.sdn
    freebsd-qemu.sdn
    windows-qemu.sdn
    trace32-stm.sdn
    vscode-test.sdn
    native.sdn                 (default: run locally)
```

Docker Compose files remain for CI workflows but the Simple test runner uses SDN configs.

---

## 6. Risk Analysis

| Risk | Severity | Mitigation |
|------|----------|------------|
| WASM adapter wiring breaks existing tests | Low | Existing 36 tests validate; add integration test |
| Container API abstraction too generic | Medium | Start with 2 backends (docker, qemu), iterate |
| VSCode headless tests flaky in Xvfb | Medium | Use `xvfb-run` with fixed resolution; retry logic |
| SDN config proliferation | Low | Keep minimal: 5-7 environments initially |
| QEMU broker refactoring breaks pooling | Medium | Keep broker as implementation detail behind new API |
| @environment annotation parsing conflicts | Low | Uses distinct prefix, no overlap with existing tags |
| LLVM WASM path requires LLVM 16+ on CI | Low | CI already has LLVM 18; local devs may need install |

---

## 7. Recommendations

### Workstream Priority Order

1. **WS-1: WASM backend** (smallest, highest value) — wire adapter, add E2E test
2. **WS-2: Environment lib** (foundation for WS-3 and WS-4) — unified API + SDN configs
3. **WS-3: @environment() routing** (depends on WS-2) — annotation + test runner integration
4. **WS-4: VSCode container testing** (depends on WS-2 + WS-3) — Dockerfile + CI

### Alternative Approaches Considered

**WASM via Emscripten instead of LLVM+wasm-ld:**
- Rejected: Emscripten adds unnecessary JavaScript glue; WASI is cleaner for CLI tools

**Nix instead of Docker for isolation:**
- Rejected: Docker/Podman already deeply integrated; Nix adds another dependency

**Test environments as code (Pulumi/Terraform) instead of SDN:**
- Rejected: Overkill for test environments; SDN is native to Simple

**WebDriver instead of Xvfb for VSCode testing:**
- Rejected: `@vscode/test-electron` already handles Electron lifecycle; just needs virtual display

---

## Cross-References

- Requirements: `doc/requirement/wasm_env_infra.md`
- Plan: `doc/plan/wasm_env_infra.md` (Phase 4)
- Design: `doc/design/wasm_env_infra.md` (Phase 4)
