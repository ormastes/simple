# `compile_remote_binary` is a fixed stub, not a compiler (blocks Notebook RemoteExec cross-cell VALUE state)

**Filed:** 2026-08-07
**Context:** Stream K, task K4 (`RemoteExec` NotebookExecutor) —
`doc/03_plan/agent_tasks/notebook_lanes_parallel_plan_2026-08-07.md`,
`doc/05_design/app/tools/notebook_lanes_architecture.md` §4.3.

## What's wrong

`src/lib/nogc_sync_mut/debug/remote/exec/compiler_bridge.spl:24-28`:

```
pub fn compile_remote_binary_in_dir(source: text, arch: Architecture, base_addr: i64, tmpdir: text) -> Result<[i32], text>:
    match arch:
        Architecture.Arm32: Ok(arm32_return_zero_bytes())
        Architecture.RiscV32: Ok(rv32_return_zero_bytes())
        _: Err("unsupported remote JIT arch")
```

`source` (the cell/test code text) is accepted but never read. Every call, for
every architecture, returns the same fixed "return 0" byte sequence
(`arm32_return_zero_bytes()` / `rv32_return_zero_bytes()`). The function's own
docstring says as much ("Current behavior emits tiny target-native stubs that
return 0 so the upload/execute path can be exercised while the full compiler
pipeline is being stabilized"), but nothing downstream treats it as
provisional — the test runner's `jit(remote(...))` lane
(`test_executor_composite_jit_generic.spl`) and the new
`src/lib/nogc_sync_mut/notebook/remote_exec.spl` (Stream K, K4) both call it
as if it compiles real semantics.

## Impact

`RemoteExec.execute_cell()` (K4) compiles each notebook cell's source through
this bridge before uploading/running it on the remote target. Because the
bridge ignores `source`, no two cells can ever produce distinct compiled
behavior — a `val x = 42` cell and a `fn f(): 2` cell upload/execute
byte-for-byte identical machine code. This blocks the literal "3 cells with
cross-cell state (val → fn → call)" proof the K4 plan asks for at the
compiled-code level.

What DOES still work through the existing pipeline, independent of this bug:
target-memory/session persistence — the same QEMU/OpenOCD/GHDL/T32 process
(and therefore its RAM) stays live across `execute_cell()` calls until
`reset()`/`shutdown()` tears it down. `RemoteExec`'s integration spec
(`test/02_integration/app/tools/notebook/remote_exec_qemu_rv32_spec.spl`)
proves that instead, and states explicitly that it is not the same thing as
cell-code-driven state.

## Unblock condition

`compile_remote_binary_in_dir` (or a successor) must actually compile
`source` — through the existing Simple compiler pipeline targeting the
requested `Architecture`, not a hand-rolled stub — so distinct cell/test
source produces distinct uploaded bytes. Once that lands, `RemoteExec`
requires no changes: it already passes the real cell `code` text through
verbatim (`remote_exec.spl`'s `compile_remote_binary(code, self.arch,
self.memory_map.code_start)`), so the K4 plan's literal val → fn → call
cross-cell assertion becomes provable without touching this file again.

## Verification 2026-08-17 (content classification) — LIVE, and this one IS silent

Confirmed live by reading `src/lib/nogc_sync_mut/debug/remote/exec/compiler_bridge.spl`
(36 lines total). `compile_remote_binary_in_dir` matches on `arch` and returns
`Ok(arm32_return_zero_bytes())` / `Ok(rv32_return_zero_bytes())`, which are
literal constants — `[0x00, 0x20]` (`movs r0, #0`) and
`[0x13, 0x05, 0x00, 0x00]` (`addi a0, x0, 0`). The `source` parameter is threaded
through every function in the file and **never read**.

Unlike the CUDA row above, this returns `Ok` — a caller compiling any program
gets a successful-looking result whose payload always returns 0. That is the
silent-wrong-result class exactly. Severity as filed (P2) is understated for the
`Ok` wrapper specifically; the honest shape would be `Err` until a real backend
lands.

Not proven: no `Results:` line —
`test/02_integration/app/tools/notebook/remote_exec_qemu_rv32_spec.spl` needs a
QEMU lane and was not run while the bootstrap holds the host.
