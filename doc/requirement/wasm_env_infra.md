# WASM Backend + Environment Infrastructure — Requirements

**Feature ID:** WASM-ENV-INFRA
**Date:** 2026-03-14
**Status:** Phase 1 — Requirements (pending approval)

---

## Motivation

Three related infrastructure gaps need to be addressed together because they share
execution-environment concerns:

1. The WASM backend is 95% complete but not wired into the compilation pipeline
2. Container/QEMU test infrastructure is fragmented across 10+ modules with no unified API
3. VSCode extension tests require a display server; this headless machine cannot run them
4. Test environment routing (`@environment()`) would unify how tests declare their runtime needs

Solving these together yields a **unified environment abstraction** that serves compilation
targets (WASM), test execution (container/QEMU/HW debugger), and plugin validation (headless VSCode).

---

## Scope

### In Scope

#### WS-1: WASM Backend Completion
- **REQ-W01:** Wire `WasmCodegenAdapter.compile_module()` to call `MirToWat.translate_module()`
- **REQ-W02:** LLVM-based WASM path: ensure `llc` + `wasm-ld` pipeline works for wasm32-wasi/wasm64-wasi
- **REQ-W03:** Unified backend selection: `--target=wasm32` auto-selects best path (standalone WAT for debug, LLVM for release)
- **REQ-W04:** End-to-end test: compile a Simple program to `.wasm`, run it via `wasmtime`/`wasmer`
- **REQ-W05:** WASI stdlib shim: minimal I/O (print, file read/write) for WASM targets

#### WS-2: Environment Library (`std.env` / `lib/env`)
- **REQ-E01:** Unified `Environment` type with variants: `Native`, `Container(config)`, `Qemu(config)`, `Remote(config)`, `HwDebugger(config)`
- **REQ-E02:** SDN-based environment configs in `config/environments/*.sdn` — each file defines one named environment
- **REQ-E03:** Environment registry: load all configs, select by name (`--env=freebsd-qemu`, `--env=docker-isolation`)
- **REQ-E04:** Container lifecycle API: `env.start()`, `env.exec(cmd)`, `env.copy_to(src, dst)`, `env.stop()` — wraps docker/podman
- **REQ-E05:** QEMU lifecycle API: same interface as container, wraps `qemu_manager.spl` functionality
- **REQ-E06:** HW debugger environment: wraps TRACE32 container or direct USB connection
- **REQ-E07:** Config selection: SDN file can specify `arch`, `os`, `runtime`, `capabilities` requirements

#### WS-3: Test Environment Routing
- **REQ-T01:** `@environment(name)` file-level annotation — declares required execution environment
- **REQ-T02:** `@environment(container)`, `@environment(qemu:freebsd)`, `@environment(hw:trace32)` — shorthand forms
- **REQ-T03:** Test runner auto-routes: reads `@environment()` tag, looks up config from registry, starts environment, runs test inside it
- **REQ-T04:** Fallback behavior: if environment unavailable, skip test with clear message (not fail)
- **REQ-T05:** Composable: `@environment()` + `@mode:` + `@platform:` all work together
- **REQ-T06:** Environment pooling: reuse running containers/VMs across test files (integrate with existing `qemu_broker.spl`)

#### WS-4: VSCode Plugin Container Testing
- **REQ-V01:** Dockerfile for headless VSCode testing (Xvfb + Electron)
- **REQ-V02:** Container config in `config/environments/vscode-test.sdn`
- **REQ-V03:** Run existing TypeScript E2E tests (`npm test`) inside container via environment lib
- **REQ-V04:** CI workflow: headless VSCode tests as part of containerized-tests pipeline
- **REQ-V05:** Migrate VSCode extension host logic to Simple where feasible (TypeScript bridge remains for VSCode API)

### Out of Scope
- Full VSCode extension rewrite to Simple (keep TypeScript bridge)
- Browser-based WASM execution (only WASI for now)
- GPU passthrough for container/QEMU environments
- Kubernetes-based test orchestration
- New WASM-specific optimizations (use existing MIR optimizer + wasm-opt)

---

## Acceptance Criteria

### WS-1: WASM
- [ ] `bin/simple build --target=wasm32 examples/hello.spl` produces a working `.wasm` file
- [ ] `wasmtime run hello.wasm` prints "Hello, World!"
- [ ] Both paths work: standalone WAT (debug) and LLVM (release)
- [ ] Backend selector correctly routes wasm32 → WAT (debug) / LLVM (release)

### WS-2: Environment Lib
- [ ] `config/environments/docker-isolation.sdn` defines a container environment
- [ ] `config/environments/freebsd-qemu.sdn` defines a QEMU VM environment
- [ ] `Environment.from_config("docker-isolation")` returns a usable environment object
- [ ] `env.start()` → `env.exec("bin/simple test test.spl")` → `env.stop()` works end-to-end
- [ ] All existing container/QEMU code migrated to use the unified API

### WS-3: Test Routing
- [ ] `# @environment(container)` in a test file causes it to run in Docker
- [ ] `# @environment(qemu:freebsd)` runs the test in a FreeBSD QEMU VM
- [ ] Missing environment → skip (not error)
- [ ] `bin/simple test --env=container` overrides to run all tests in containers
- [ ] Environment pooling reuses running containers across test files

### WS-4: VSCode Testing
- [ ] `bin/simple test --env=vscode-test` runs VSCode E2E tests in a container
- [ ] CI pipeline includes headless VSCode test job
- [ ] Tests pass without a physical display

---

## I/O Examples

### Example 1: WASM compilation
```bash
$ bin/simple build --target=wasm32 examples/hello.spl
[build] Compiling examples/hello.spl → build/wasm32/hello.wasm
[build] Using backend: wat (debug mode)
[build] Done (0.8s)

$ wasmtime run build/wasm32/hello.wasm
Hello, World!
```

### Example 2: Environment SDN config
```sdn
# config/environments/docker-isolation.sdn
environment {
    name: "docker-isolation"
    type: "container"

    container {
        runtime: "auto"          # docker or podman
        image: "simple-test:latest"
        dockerfile: "tools/docker/Dockerfile.test-isolation"
        read_only: true
        cap_drop: ["ALL"]
        network: "none"
        resources {
            cpus: 2
            memory_mb: 1024
        }
    }

    requirements {
        arch: ["x86_64", "aarch64"]
        os: ["linux"]
    }
}
```

### Example 3: QEMU environment config
```sdn
# config/environments/freebsd-qemu.sdn
environment {
    name: "freebsd-qemu"
    type: "qemu"

    qemu {
        image_path: "images/freebsd-14.qcow2"
        arch: "x86_64"
        cpus: 2
        ram_mb: 2048
        ssh_port: 2222
        accel: "kvm"           # fallback to tcg if unavailable
        snapshot: true          # use snapshots for fast reset
    }

    # exe selection: which binary to use inside the VM
    exe {
        default: "bin/simple"
        alternatives: {
            "cross-compiled": "bin/simple-freebsd-amd64"
            "bootstrap": "bin/bootstrap/cpp/simple"
        }
        select: "cross-compiled"    # which alternative to use
    }

    requirements {
        arch: ["x86_64"]
        capabilities: ["kvm"]
    }
}
```

### Example 4: Test with @environment annotation
```simple
# @environment(docker-isolation)
# @mode: native

import std.spec { describe, it, expect }

describe "Sandboxed compilation":
    it "compiles and runs in isolation":
        var result = shell("bin/simple run examples/hello.spl")
        expect(result.stdout).to_contain("Hello")
```

### Example 5: HW debugger environment
```sdn
# config/environments/trace32-stm.sdn
environment {
    name: "trace32-stm"
    type: "hw_debugger"

    hw_debugger {
        tool: "trace32"
        container_compose: "config/t32/trace32_x11_container.compose.yml"
        port: 20000
        target_board: "stm32f4"
    }

    exe {
        default: "bin/simple-arm32"
        select: "default"
    }

    requirements {
        capabilities: ["usb", "trace32"]
    }
}
```

---

## Dependencies

| Dependency | Status | Notes |
|-----------|--------|-------|
| WASM backend (WAT codegen) | 95% complete | Only adapter wiring needed |
| LLVM WASM target | Complete | wasm32-wasi supported via llc+wasm-ld |
| Docker runner | Working | src/app/test/docker_runner.spl |
| QEMU manager | Working | src/app/vm/qemu_manager.spl |
| QEMU broker | Working | src/app/test_daemon/qemu_broker.spl |
| Execution strategy | Working | src/app/test_runner_new/execution_strategy.spl |
| Test mode annotations | Working | @mode, @skip_mode, @platform |
| Environment detection | Working | src/lib/nogc_sync_mut/spec/env_detect.spl |
| VSCode extension | Working | TypeScript + WASM LSP bridge |
| TRACE32 container | Working | config/t32/ |

---

## Cross-References

- Research: `doc/research/wasm_env_infra.md`
- Plan: `doc/plan/wasm_env_infra.md` (Phase 4)
- Design: `doc/design/wasm_env_infra.md` (Phase 4)
- System Tests: `test/system/wasm_env_infra_spec.spl` (Phase 6)
