# Self-hosted JIT execution owner missing from audited paths

Status: open REQ-002 execution and certification blocker. Source audit only,
2026-10-03; no runtime attempt. This finding covers the specific paths below,
not every backend or external provider in the repository.

## Evidence

| Inspected source | Observed contract |
|---|---|
| `src/app/io/_CliCommands/run_commands.spl:136` | Source run calls `interpret_file`; the optional execution receipt identifies actual interpreter execution, including fallback for a JIT request. |
| `src/compiler/80.driver/driver_api_interpret.spl:28` | After the separately admitted SMF cache route, explicitly sets `CompileMode.Interpret` at line 38 and invokes the compiler driver. SMF execution is not a JIT witness. |
| `src/compiler/70.backend/backend/jit_interpreter.spl:151` | The apparent hybrid backend delegates compile/execute to `LocalExecutionManager`; selecting it alone cannot establish native execution. |
| `src/compiler/95.interp/execution/mod.spl:12` | Execution manager imports the shared `app.io.jit_sffi` implementation, despite comments describing a Rust-backed manager. |
| `src/app/io/jit_sffi.spl:85` | `rt_exec_manager_create` rejects explicit LLVM/Cranelift requests with handle 0. The accepted soft path stores source at line 105; `_run_code` at line 122 invokes `interpret_file`; backend identity is interpreter. It is not a machine-code executor. |
| `src/compiler/10.frontend/core/interpreter/mod.spl:264` | `core_jit_interpret` initializes tracking and invokes the ordinary core pipeline. |
| `src/compiler/10.frontend/core/interpreter/jit.spl:189` | `jit_try_compile` marks a name compiled; `jit_try_execute` at line 198 returns 0 for marked names, without compiling or invoking machine code. These functions cannot certify JIT execution. |
| `src/compiler/99.loader/jit_instantiator.spl:329` | This compatibility instantiator uses `_fake_compile_bytes` and `_next_fake_address`. Its success result is not proof of executable mapping/invocation. The separate loader implementation was not exhaustively audited. |
| `src/compiler/95.interp/execution/tiered_jit_manager.spl:10` | Native `rt_jit_*` extern bridge is documented as a Rust manager boundary; it does not supply an audited pure-Simple self-hosted execution owner. |

There are two distinct gaps. The strict differential harness has no admitted
positive JIT witness. More fundamentally, the audited self-hosted source-run
and compatibility paths do not perform actual JIT compilation and invocation.
Adding a marker to those paths would mislabel interpretation or tracking state.
Strict environment variables and hot-call counters are requests, not execution
evidence. The newly owned interpreter receipt can certify only its own route.

## Minimum real implementation contract

1. Accept an admitted typed MIR module and its complete dependency closure,
   with canonical runtime symbol and target ABI bindings.
2. Emit native code through a real backend; map it into executable memory,
   resolve imports/relocations, and retain code/data ownership for every live
   callable and closure. Enforce platform permission and unload rules.
3. Invoke the actual mapped entrypoint using the canonical argument/result ABI,
   including collection and closure lifetimes. Compilation/loading/invocation
   failure must remain failure in strict mode, with no interpreter substitute.
4. Emit an execution-owner receipt only after actual invocation, identifying
   requested and actual engine/backend, fallback state, and the executed
   source/artifact identity. Compile intent, a nonzero handle, or a cached name
   alone cannot produce this witness.
5. Execute shared semantic fixtures and negative admission cases through that
   owner. Retain exact outputs, exits and receipts before marking REQ-002 parity.

Existing native LLVM code generation may be reusable infrastructure, but building
an executable and starting an AOT subprocess is the native lane, not evidence of
an in-process JIT route. Existing SMF loading must likewise be identified by its
actual execution route. Do not relabel either to fill the JIT acceptance column.

No engine implementation is authorized by this note before an admitted test
runner is available. REQ-002 remains open; no global claim that every possible
JIT provider is absent is made here.
