 # Pure Simple Remote Interpreter + JIT Baremetal Plan
 
 **Date:** 2026-03-23
 **Status:** Planning
 **Scope:** Restore a real Pure Simple remote baremetal execution architecture, then add a shared remote interpreter payload/protocol, and only after that add target-side or target-loaded JIT execution where justified.
 
 ---
 
 ## Executive Summary
 
 This plan is for the Pure Simple path only.
 
 It is based on the current repo state and recent history:
 
 - real Pure Simple baremetal compile/run support existed
 - remote debug/backend plumbing existed
 - bridge-based remote interpreter wiring existed
 - a completed target-resident remote interpreter with JIT for all current hardware was not found in history
 
 The repo drift happened because three different concepts were mixed together:
 
 1. baremetal native execution
 2. remote debug transport
 3. remote interpreter / remote JIT
 
 They must be separated again.
 
 The recommended implementation order is:
 
 1. restore the last known Pure Simple baremetal target matrix
 2. define one shared remote execution abstraction
 3. implement a real target-resident remote interpreter for one reference target
 4. extend the same protocol to the rest of the hardware/simulation backends
 5. only then add remote JIT
 
 Remote JIT must not be the first recovery step.
 
 ---
 
 ## Historical Findings
 
 ### What Existed
 
 #### 1. Real baremetal compile/run path
 
 Commit `2af77ea39b` implemented a real Pure Simple compile-and-run pipeline:
 
 - `.spl` -> LLVM IR -> object -> ELF
 - QEMU baremetal execution
 - T32 flash/run for STM targets
 
 At that point:
 
 - `src/compiler/80.driver/build/baremetal.spl` had:
   - `Riscv32`
   - `Stm32h7`
   - `Stm32wb`
 - `src/lib/nogc_sync_mut/test_runner/test_executor_composite.spl` used those targets
 
 This was real baremetal execution, not a target-side remote interpreter.
 
 #### 2. Remote debug/backend infrastructure
 
 Commit `a61025c513` added remote debug support:
 
 - GDB-MI client
 - TRACE32 client
 - backend ranking / capability selection
 - DAP remote backend support
 
 This was debugger/backend infrastructure.
 It was not a completed remote interpreter runtime.
 
 #### 3. Remote interpreter bridge wiring
 
 Commit `eeb6a5fd8d` added bridge-oriented remote interpreter wiring.
 
 That historical code explicitly showed the actual state:
 
 - remote interpreter required backend-specific commands
 - remote native execution was still not implemented
 - remote loader execution was still not implemented
 
 Commit `6584eb7fe8` then added shell bridge scripts.
 Those scripts explicitly said the target-side interpreter was missing.
 
 ### What Did Not Exist
 
 No historical evidence was found for a completed target-resident remote interpreter with JIT across:
 
 - QEMU RISC-V32
 - STM32H7
 - STM32WB
 - CH32V307
 - RTL / GHDL RISC-V32 simulation
 
 The repo had real pieces, but not the full end-to-end target-side interpreter/JIT product.
 
 ---
 
 ## Current Problems
 
 ### 1. Baremetal target regression
 
 Current `src/compiler/80.driver/build/baremetal.spl` only exposes:
 
 - `Arm`
 - `X86_64`
 - `Riscv`
 
 It no longer exposes the historical target-specific configs that the composite runner expected:
 
 - `Riscv32`
 - `Stm32h7`
 - `Stm32wb`
 
 This blocks faithful recovery of the historical Pure Simple baremetal runner shape.
 
 ### 2. Composite mode drift
 
 The current Pure Simple composite runner has been reduced to:
 
 - host-interpreter fallback for `.spl`
 - direct-QEMU execution for `.elf`
 
 That means the working lane is now:
 
 - Pure Simple host runner
 - composite mode parsing/dispatch
 - direct ELF execution on QEMU
 
 It is not:
 
 - target-resident interpreter
 - target-resident JIT
 - host-to-target payload execution
 
 ### 3. Host JIT vs target JIT confusion
 
 The current repo JIT is host-side.
 
 Relevant code lives under:
 
 - `src/compiler/99.loader/loader/jit_instantiator.spl`
 - `src/compiler/99.loader/loader/module_loader.spl`
 - `src/compiler/70.backend/codegen.spl`
 
 That logic assumes host executable memory and host process semantics.
 It is not directly reusable as a target-side baremetal JIT runtime.
 
 ### 4. Backend and transport logic are mixed
 
 The repo currently mixes:
 
 - transport concerns
 - flashing/loading concerns
 - debug concerns
 - test runner dispatch concerns
 - target execution model concerns
 
 That caused fallback behavior to masquerade as “remote interpreter support”.
 
 ---
 
 ## Goals
 
 ### Primary Goal
 
 Build a real Pure Simple remote baremetal execution stack with a shared architecture and no fake fallback paths.
 
 ### Secondary Goal
 
 Make the remote interpreter implementation shared across current hardware/simulation targets as much as possible.
 
 ### Deferred Goal
 
 Add remote JIT only after remote interpreter is real and stable.
 
### Current sequencing note

Near-term execution work should focus on shared baremetal library tests, not just smoke fixtures.

That means:

- refactor at least one baremetal library workload so it can run on host and through the remote/JIT target path
- prove that first on STM32H7 real hardware
- then carry the same workload shape to `riscv32`

### Shared test-set rule

- one shared workload is the reference baremetal lib test set:
  `test/feature/app/remote_baremetal/remote_baremetal_library_workload.spl`
- host executes that workload directly
- remote/JIT targets compile the same `main()` wrapper fixture:
  `test/fixtures/remote_jit/baremetal_lib_workload_main.spl`
- once the shared workload exists, ad hoc `return 0` / `return 42` programs should remain smoke/debug helpers only, not the main proof

### Current shared workload status

- host shared workload is green in:
  `test/integration/remote_jit/baremetal_library_host_spec.spl`
- STM32H7 real hardware shared workload is green in:
  `test/integration/remote_jit/stm32h7_composite_runner_spec.spl`
- QEMU RV32 shared workload spec is now interpreter-safe in:
  `test/integration/remote_jit/qemu_rv32_composite_runner_spec.spl`
  but the live QEMU/GDB transport is still blocked on this host because only plain `gdb` is available
  and the working QEMU write path needs a target-aware RISC-V GDB for physical-memory mode
- QEMU RV32 library workload is proven through the stable semihost ELF lane in:
  `test/integration/remote_jit/qemu_rv32_library_semihost_spec.spl`
- CH32V307 real hardware direct-control lane is now proven in:
  `test/integration/remote_jit/ch32v307_composite_runner_spec.spl`
  through direct `wlink` control rather than the stale adapter path
  currently proven: probe discovery, RAM write/readback, register dump,
  and reuse of the shared workload fixture
  not yet proven: full shared-workload execution on CH32V307
- the last STM32H7 interpreter failure came from helper code using `index_of()` as if it returned an integer
- TRACE32 readiness is no longer blocked by the app-side parse bug in `src/app/debug/remote/protocol/trace32.spl`
- current host TRACE32 state is still blocked:
  `/opt/t32/bin/pc_linux64/t32rem localhost port=20000 PING` timed out with exit `124`

 ---
 
 ## Non-Goals
 
 This plan does not start by:
 
 - reviving Rust CLI composite mode
 - implementing target-side self-hosted native-code generation first
 - using ad hoc backend-specific shell scripts as the long-term design
 - treating semihosted ELF execution as equivalent to remote interpreter execution
 
 ---
 
 ## Architectural Principles
 
 ### 1. Separate execution modes clearly
 
 The implementation must distinguish:
 
 - `remote_debug`
 - `remote_native`
 - `remote_interpreter`
 - `remote_jit`
 
 These must not silently fall back into one another.
 
 ### 2. One shared host-target protocol
 
 All remote interpreter targets should use one shared protocol shape.
 
 Backend adapters may differ in transport details, but not in the logical command model.
 
 ### 3. One shared payload format
 
 Remote interpreter must consume a stable payload format produced by Pure Simple lowering.
 
 That payload should be shared across:
 
 - QEMU RISC-V32
 - STM32H7
 - STM32WB
 - CH32V307 where feasible
 - RTL / GHDL RV32 simulation
 
 ### 4. JIT is tier 2
 
 Remote interpreter is tier 1.
 Remote JIT is tier 2.
 
 If the interpreter protocol is not stable, JIT will drift and break faster.
 
 ### 5. No hidden fallback
 
 If a target or backend cannot run a given mode, the result must be:
 
 - explicit error
 - explicit blocked state
 - explicit unsupported state
 
 Never silent host fallback.
 
 ---
 
 ## Target Matrix
 
 ### Phase 1 targets
 
 - `riscv32` via QEMU
 
 This is the reference implementation target.
 
 ### Phase 2 targets
 
 - `stm32wb` via TRACE32/OpenOCD
 - `stm32h7` via TRACE32/OpenOCD
 - `ch32v307` via WCH-Link if memory-load/run semantics are sufficient
 
 ### Phase 3 targets
 
 - `riscv32_sim_vhdl` via GHDL mailbox transport
 
 This should become the cleanest simulation-backed remote interpreter lane because it avoids unstable host debugger assumptions.
 
 ---
 
 ## Proposed Mode Model
 
 ### `native(baremetal(target))`
 
 Meaning:
 
 - compile source to target ELF
 - flash/load/run as a target-native program
 
 ### `interpreter(remote(baremetal(target)))`
 
 Meaning:
 
 - load a remote interpreter payload/protocol into the target runtime
 - the target executes interpreted instructions or bytecode
 - results come back through a shared host-target protocol
 
 ### `jit(remote(baremetal(target)))`
 
 Meaning:
 
 - use the same remote payload/protocol shell
 - but execute a compiled code payload or target-generated code
 
 This mode must reuse the same transport and result protocol as `remote_interpreter`.
 
 ---
 
 ## Shared Remote Execution Architecture
 
 ```text
 Test Runner
   -> Composite Mode Parser
   -> Remote Execution Dispatcher
   -> Remote Backend Adapter
   -> Shared Host-Target Protocol
   -> Target Runtime
   -> Result Parser
 ```
 
 ### Shared host-side layers
 
 #### 1. Remote dispatcher
 
 Owns:
 
 - mode selection
 - target selection
 - capability checking
 - fail-fast unsupported/error behavior
 
 #### 2. Remote transport adapter
 
 Owns transport-specific operations:
 
 - write memory
 - read memory
 - run / halt / reset
 - poll status
 - collect output
 
 Examples:
 
 - QEMU GDB adapter
 - TRACE32 adapter
 - OpenOCD adapter
 - WCH-Link adapter
 - GHDL mailbox adapter
 
 #### 3. Remote payload builder
 
 Owns:
 
 - lowering a Simple test program into a remote interpreter payload
 - serializing constants, functions, and entrypoint metadata
 - versioning the payload format
 
 #### 4. Remote result parser
 
 Owns:
 
 - stdout capture
 - summary capture
 - error capture
 - machine-readable result decoding
 
 ### Shared target-side layers
 
 #### 1. Remote runtime core
 
 Owns:
 
 - command loop
 - opcode decode
 - call stack
 - register/locals model
 - control flow
 
 #### 2. Remote runtime memory
 
 Owns:
 
 - constant pool access
 - fixed stack arena
 - fixed heap arena if allowed
 - handles / object references for restricted runtime subset
 
 #### 3. Remote runtime host I/O
 
 Owns:
 
 - test output
 - summary output
 - structured error reporting
 
 #### 4. Remote runtime transport binding
 
 Owns:
 
 - mailbox/register/memory protocol access
 - not interpreter semantics
 
 ---
 
 ## Payload Format
 
 The remote interpreter payload should be architecture-neutral.
 
 ### Minimum payload sections
 
 - header
 - protocol version
 - target/runtime capability flags
 - constant pool
 - string table
 - function table
 - code blocks / bytecode blocks
 - entrypoint id
 - optional debug symbol table
 
 ### Requirements
 
 - deterministic serialization
 - no host executable-memory assumptions
 - small enough to load into target memory
 - explicit versioning
 - compatible with interpreter-first execution
 
 ### Why this matters
 
 This is the main sharing point between interpreter and later JIT.
 
 If the payload format is stable, the repo can later:
 
 - interpret it on target
 - compile it on target
 - or have the host compile it into target-loadable code
 
 without changing the test runner protocol.
 
 ---
 
 ## Protocol Design
 
 The host-target protocol must be shared.
 
 ### Logical commands
 
 - `HELLO`
 - `RESET_VM`
 - `LOAD_PAYLOAD`
 - `CALL entry`
 - `POLL_STATUS`
 - `READ_STDOUT`
 - `READ_SUMMARY`
 - `READ_ERROR`
 - `SHUTDOWN`
 
 ### Shared result states
 
 - `idle`
 - `busy`
 - `passed`
 - `failed`
 - `crashed`
 - `protocol_error`
 - `unsupported`
 
 ### Transport mappings
 
 #### QEMU RISC-V32
 
 - GDB memory write/read
 - register/control via GDB
 - semihost or ring-buffer output capture
 
 #### TRACE32
 
 - memory write/read via T32 commands
 - run/break/reset via T32 commands
 - output via AREA capture or memory buffer
 
 #### OpenOCD
 
 - memory write/read via GDB/OpenOCD
 - run/reset via monitor/GDB
 - output via memory buffer or semihost if supported
 
 #### GHDL RV32 simulation
 
 - mailbox MMIO
 - explicit testbench-driven polling
 - deterministic host transcript
 
 ---
 
 ## JIT Strategy
 
 ### Recommendation
 
 Do not start with target-side JIT compilation.
 
 Start with:
 
 - host lowering
 - target interpreter payload execution
 
 Only after that, add one of these:
 
 ### Option A. Host-compiled target-loadable code
 
 Host compiles a restricted MIR/lowered payload into target-native code.
 Target receives and runs it.
 
 Pros:
 
 - much simpler than self-hosted target JIT
 - reuses more existing host codegen infrastructure
 
 Cons:
 
 - technically closer to remote loader than self-hosted target JIT
 
 ### Option B. True target-side JIT
 
 Target receives a neutral payload and generates executable target code itself.
 
 Pros:
 
 - pure meaning of “remote interpreter with JIT”
 
 Cons:
 
 - much harder
 - needs executable RAM, relocations, cache policy, symbol model
 
 ### Recommended path
 
 Implement Option A first if “JIT mode” is needed early.
 Implement Option B only after the interpreter and loader path are already stable.
 
 ---
 
 ## Implementation Phases
 
 ## Phase 0. Restore Historical Baremetal Target Matrix
 
 **Goal:** recover the Pure Simple target matrix that the composite runner used before regression.
 
 ### Tasks
 
 - restore target variants in `src/compiler/80.driver/build/baremetal.spl`:
   - `Riscv32`
   - `Stm32h7`
   - `Stm32wb`
 - restore factory functions:
   - `baremetal_config_riscv32()`
   - `baremetal_config_stm32h7()`
   - `baremetal_config_stm32wb()`
 - verify current linker/startup/runtime paths still exist or replace stale ones
 - align `src/lib/nogc_sync_mut/test_runner/test_executor_composite.spl` to the restored config set
 
 ### Exit Criteria
 
 - Pure Simple composite runner can target the historical target set again
 - no missing symbol/config errors for those target configs
 
 ## Phase 1. Reintroduce a Shared Pure Simple Remote Module
 
 **Goal:** recover remote execution architecture without reviving old stub-based drift.
 
 ### Tasks
 
 - create or restore a shared remote execution module for Pure Simple
 - split responsibilities:
   - dispatcher
   - transport adapter
   - payload builder
   - result parser
 - remove silent host fallback semantics from remote modes
 - make unsupported states explicit
 
 ### Exit Criteria
 
 - remote execution path is explicit and inspectable
 - no `.spl -> host interpreter` fallback when remote interpreter mode is selected
 
 ## Phase 2. Implement Shared Payload Format
 
 **Goal:** give remote interpreter a real runtime input format.
 
 ### Tasks
 
 - define payload schema and versioning
 - add serializer in Pure Simple
 - add test fixtures for tiny payloads
 - add parser/validator on target runtime side
 
 ### Exit Criteria
 
 - tiny payload round-trips in tests
 - payload version mismatch is reported clearly
 
 ## Phase 3. Implement Target Remote Interpreter Runtime for `riscv32`
 
 **Goal:** make one real target-resident remote interpreter work.
 
 ### Tasks
 
 - implement target-side runtime loop for `riscv32`
 - support a restricted instruction/runtime subset:
   - integer ops
   - comparisons
   - branches
   - fixed calls
   - output
   - return / fail
 - add a fixed memory model
 - define output and summary channels
 
 ### Exit Criteria
 
 - a small Pure Simple test payload runs on target through the remote interpreter
 - no host fallback is used
 
 ## Phase 4. QEMU RISC-V32 Reference Backend
 
 **Goal:** make QEMU the first real end-to-end backend.
 
 ### Tasks
 
 - implement `RemoteTransport` adapter for QEMU/GDB
 - use shared payload/protocol
 - load payload into target memory
 - run interpreter loop on target
 - collect machine-readable output
 
 ### Exit Criteria
 
 - `interpreter(remote(baremetal(riscv32)))` executes a real target-side payload on QEMU
 - system tests prove payload load, execution, output, summary
 
 ## Phase 5. STM32 Hardware Backends
 
 **Goal:** extend the exact same architecture to real hardware.
 
 ### Tasks
 
 - TRACE32 adapter:
   - memory write
   - run/break/reset
   - output collection
 - OpenOCD adapter:
   - memory write
   - run/reset
   - output collection
 - map the same payload/protocol onto:
   - `stm32wb`
   - `stm32h7`
 
 ### Exit Criteria
 
 - same protocol works on both STM targets
 - failures classify correctly as repo bug vs host/tooling blocker
 
 ## Phase 6. CH32V307 / WCH-Link Backend
 
 **Goal:** support the current RISC-V hardware lane where practical.
 
 ### Tasks
 
 - assess whether WCH-Link supports the required load/run/read semantics cleanly
 - implement adapter only if capability coverage is sufficient
 - otherwise document exact blocker and leave backend unsupported
 
 ### Exit Criteria
 
 - either a real adapter exists
 - or unsupported is explicit and tested
 
 ## Phase 7. RTL / GHDL Simulation Backend
 
 **Goal:** provide a debugger-independent simulation-backed remote interpreter lane.
 
 ### Tasks
 
 - use mailbox transport, not semihost-only signaling
 - define mailbox MMIO contract
 - implement host-side testbench driver
 - implement target-side mailbox runtime binding
 - add `riscv32_sim_vhdl` or equivalent target spelling
 
 ### Exit Criteria
 
 - simulation-backed remote interpreter runs end to end
 - `simple test` can use the simulation lane
 
 ## Phase 8. Remote JIT
 
 **Goal:** add JIT without breaking the interpreter architecture.
 
 ### Tasks
 
 - decide whether first JIT mode is:
   - host-compiled target-loadable code
   - or true target-side JIT
 - reuse:
   - payload format
   - transport
   - result protocol
 - add executable-memory region policy for target
 - add relocation / symbol contract
 - add strict capability detection
 
 ### Exit Criteria
 
 - `jit(remote(baremetal(riscv32)))` is real
 - it shares the same transport/protocol structure as remote interpreter
 - it does not require a separate ad hoc runner architecture
 
 ---
 
 ## Shared Test Strategy
 
 ### System tests to add
 
 #### 1. Baremetal target matrix recovery
 
 - target config selection tests
 - compile/run target routing tests
 
 #### 2. Remote payload protocol tests
 
 - hello / handshake
 - load payload
 - call entrypoint
 - poll status
 - read summary
 
 #### 3. QEMU reference e2e
 
 - small arithmetic payload
 - branching payload
 - hello-world payload
 - failing payload
 
 #### 4. Hardware host-aware specs
 
 - STM32WB
 - STM32H7
 - CH32V307 if supported
 
 #### 5. Simulation e2e
 
 - GHDL mailbox protocol smoke
 - hello-world payload
 - failure-reporting payload
 
 #### 6. JIT-specific tests later
 
 - same logical test corpus as interpreter
 - compare interpreter vs JIT result parity
 
 ### Important rule
 
 Every system test must prove a real mode.
 
 Examples:
 
 - if mode is `remote_interpreter`, the test must fail if host fallback occurs
 - if mode is `remote_jit`, the test must fail if interpreter-only execution occurs
 
 ---
 
 ## Files Likely To Change
 
 ### Pure Simple runner / transport
 
 - `src/lib/nogc_sync_mut/test_runner/test_executor_composite.spl`
 - new shared remote execution module under `src/lib/nogc_sync_mut/test_runner/`
 - remote backend adapters under `src/lib/nogc_sync_mut/debug/remote/`
 
 ### Baremetal build
 
 - `src/compiler/80.driver/build/baremetal.spl`
 
 ### Target runtime
 
 - new target remote runtime modules under baremetal runtime areas
 - shared noalloc runtime support modules
 
 ### Simulation
 
 - `examples/09_embedded/fpga_riscv/rtl/`
 - `test/feature/baremetal/ghdl_riscv32_semihost_spec.spl`
 - new simulation-backed remote interpreter specs
 
 ### Specs / docs
 
 - `test/feature/app/remote_baremetal/`
 - `doc/spec/tooling/simple_test.md`
 - `doc/design/embedded_test_runner_design.md`
 
 ---
 
 ## Risks
 
 ### 1. Trying to port host JIT directly
 
 This is the highest-risk mistake.
 Host JIT assumptions do not map cleanly to baremetal target execution.
 
 ### 2. Repeating bridge-script drift
 
 The old bridge-script approach is useful as evidence of intended control flow, but not as the architecture.
 
 ### 3. Confusing native baremetal with remote interpreter
 
 Running an ELF on QEMU is not the same as a target-side interpreter runtime.
 
 ### 4. Hardware-specific divergence
 
 If each target gets its own protocol, the system will break again.
 
 ---
 
 ## Definition of Done
 
 This work is done when all of the following are true:
 
 - Pure Simple baremetal target matrix is restored
 - `interpreter(remote(baremetal(riscv32)))` runs a real target-side payload on QEMU
 - the same logical protocol is reused for STM32 targets
 - simulation-backed RV32 remote interpreter works through GHDL mailbox transport
 - remote interpreter mode has no hidden host fallback
 - remote JIT, if added, reuses the same protocol and payload architecture
 - docs and system specs describe the real execution model precisely
 
 ---
 
 ## Recommended Immediate Next Steps
 
 1. Restore `Riscv32`, `Stm32h7`, and `Stm32wb` target configs in `baremetal.spl`.
 2. Reintroduce a Pure Simple shared remote execution module with explicit mode separation.
 3. Define the remote payload schema and version header.
 4. Implement the first real target-side interpreter runtime for `riscv32` on QEMU.
 5. Add system tests that fail if remote mode silently falls back to host interpretation.
 
 ---
 
 ## 2026-03-23 Implementation Update
 
 Implemented in Pure Simple:
 
 - `run_test_file_jit()` in `src/lib/nogc_sync_mut/test_runner/test_executor_composite.spl` no longer falls back to the host interpreter.
 - The JIT runner now attempts a real `source -> CompilerBridge.compile(...) -> QEMU adapter -> RemoteExecutionManager.execute_bytes(...)` flow for `riscv32` and `arm32`.
 - The shared remote JIT stack was repaired enough to load and partially execute:
   - mutable allocator path fixed
   - uploader chunk constant visibility fixed
   - GDB MI `wait_for_stop()` added
   - register index to register name mapping added
   - QEMU RV32 write path now retries with QEMU physical memory mode enabled
   - adapters now unwrap `Option<GdbMiClient>` correctly
 
 Verified current state:
 
 - `bin/simple test test/feature/app/remote_baremetal/remote_baremetal_qemu_hello_spec.spl --quick` passes
 - `bin/simple test test/integration/remote_jit/stm32h7_e2e_jit_spec.spl --quick` still fails with `semantic: type mismatch: cannot convert enum to int`
 - `bin/simple test test/system/remote_jit_spec.spl --quick` gets much further than before but is still not green
 
 Current remaining blockers:
 
 - the shared QEMU system spec still fails in its uploader mock (`method len not found on type nil`)
 - the real QEMU RV32 write/read/verify lane still fails with `called unwrap on None`
 - `run_test_file_jit()` is now a minimal program runner, not yet a full target-side SSpec runner:
   - it compiles the source file directly as a target program
   - it treats `return_value == 0` as pass
   - it does not yet capture and parse semihost output for hello-world / SSpec assertions
 - STM JIT coverage is still blocked by failures in the STM-specific hardware spec, not by the old interpreter fallback
 
 Recommended next implementation order after this update:
 
 1. Fix the uploader mock in `test/system/remote_jit_spec.spl` so the shared spec goes green.
 2. Fix the QEMU RV32 `unwrap None` path in the real write/read/verify lane.
 3. Add a dedicated Pure Simple QEMU JIT smoke using a minimal program source that returns `0`.
 4. Extend the JIT runner to capture and parse semihost output.
 5. Fix the STM32H7 E2E spec failure and rerun on real hardware.
