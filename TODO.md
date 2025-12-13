# Tedo 

### ruby bdd style framework
### pydoctest like tests
### llm friendly 
#### show only limited interface to minimize context size
#### infra about system test public class/struct touch coverage
#### system test mock usage limit or prevent.
#### infra about integration test public function touch coverage
### update lanagauage spec << convension over config
### gui support
#### ruby rails spring like framework
#### tui


## Completed

### Embedded Support (src/embedded/)
**Startup code:**
- ARM Cortex-M (M0, M3, M4, M7) - vector tables, NVIC, SysTick
- RISC-V (RV32, RV64) - CSR, PLIC, CLINT
- Linker scripts for both architectures

**Teardown module:**
- Settlement SSMF parsing for embedded targets
- Intel HEX and S-Record output formats
- Target configs: STM32F103, STM32F4, nRF52832, ESP32-C3, RISC-V QEMU

**Variants module:**
- Feature flags: `no-float`, `no-alloc`, `no-thread`, `no-gc`
- Presets: `minimal`, `embedded-tiny`, `embedded-small`
- Fixed-point math (Q16.16) for float-less targets
- Static containers for alloc-less targets
- Cooperative scheduler for thread-less targets
- Memory pools and arenas for GC-less targets

---

## Ignored Tests (features not yet implemented)

### Generator JIT codegen
- **Test:** `jit_generator_dispatcher_yields_and_restores`
- **File:** `src/compiler/tests/generator_codegen.rs:14`
- **Reason:** Requires stable block layout hookup; dispatcher path covered in runtime test

### Unit conversion methods
- **Test:** `interpreter_unit_family_to_base`
- **File:** `src/driver/tests/interpreter_types.rs:473`
- **Reason:** Unit conversion methods (`.to_m()`) not yet implemented

### Embedded panic customization
- **Test:** `doc test src/embedded/src/lib.rs - (line 22)` (ignored)
- **File:** `src/embedded/src/lib.rs`
- **Reason:** Doc-test kept ignored for no_std placeholder entry macro
- **Status:** Postponed; keep ignored until a host-friendly doctest harness exists

---  
## add convention over config to rule on language spec
## Postponed

### GPU backends
- WGPU/WebGPU backend integration
- Metal backend (Apple)

### 32-bit architecture support
**Status:** Deferred - requires LLVM backend
**Reason:** Cranelift does not support 32-bit (ARM32 was removed)
