# macOS Phase2 MCP debug enum duplicate symbols

Status: focused fix and native regression PASS; full Phase2 rerun pending.
Base: `e6ffda6849e6aa7fe01a7d23ddc71e9773286532`.
Owner: `/root/stage2_after_borrow_fix`.
Independent Astra review: `/root/mac_watchdog_sampler`, PASS relayed by root.

## Cause and change

Phase2 `mcp_build` failed on three strong definitions shared by the generated
Simple objects and `host_gpu_core_c_runtime/libsimple_runtime.a(runtime_native.o)`:

- `lib__nogc_sync_mut__debug__remote__session_model__DebugExecutionMode_dot_to_string`
- `lib__nogc_sync_mut__debug__remote__session_model__DebugTransportKind_dot_to_string`
- `lib__nogc_sync_mut__debug__remote__types__Architecture_dot_to_string`

The C runtime copied library-level enum formatters already owned by
`src/lib/nogc_sync_mut/debug/remote/session_model.spl` and `types.spl`.
Its architecture switch also lacked Avr/I8086/Wasm32/Xtensa. Delete only these
three duplicate C functions; retain the existing pure-Simple implementations.
All `rt_*` APIs and the Simple methods remain. There is no weak-symbol fallback,
linker duplicate suppression, additional allocation, or hot-path work.

## Producer and retained evidence

Worktree: `/Users/ormastes/simple-tmp/macos-mcp-symbol-20260923`.
Evidence: `build/native_probe/debug_enum_owner/` in that worktree.
Admitted Stage2 compiler:

`/Users/ormastes/simple-tmp/macos-bootstrap-restart-20260922/build/bootstrap/macos-enforced-bd544-stage2/stage3/aarch64-apple-darwin/stage2-admitted/simple`

SHA256: `0c65162af9c89bdb9c6583ca91820f795231c9bf4c451b6a69ea66794c66c084`.
Admission status/hash and frozen runtime capsule verified before execution;
producer hash checked afterwards. LLVM23.1.1; native fixture threads1 and
separate cache. No seed was substituted as a test runner.

Original Phase2 logs/objects are under the P0 worktree:
`build/evidence/macos-enforced-bd544/phase2-stage2-scalar-return-e6ffda6/`.
The failed object leaf is
`cache/tool_builds/stage2/0c65162af9c89bdb9c6583ca91820f795231c9bf4c451b6a69ea66794c66c084/native-objects-zUeD1e`.

## Focused verification

1. Original MCP generated objects `mod_85.o` and `mod_86.o`, linked with the
   retained original runtime object using Apple `ld -r -arch arm64`, fail with
   exactly the three duplicates. Log: `link-red/link.log`.
2. Compile the modified runtime object and repeat the same relocatable link:
   PASS. The combined object has one strong definition of each method.
   Logs: `link-green/compile.log`, `link-green/link.log`.
3. Compare complete `nm -gU` export lists: exactly those three definitions
   disappear from the runtime object; all other globals, including every
   `rt_*` definition, remain. Lists: `link-{red,green}/exports.txt`.
4. The native fixture calls all 19 enum variants and prints its real PASS
   marker. Baseline and changed runtime both pass behavior; because this
   isolated source root uses `src__lib__`, this is not the red link proof.
   Logs: `red/build.log`, `green/build.log`, `green/run.log`.
5. Copy the original core-C archive into `mcp-relink/`, replace only its
   `runtime_native.o`, and relink the complete retained MCP object archive
   with its original hosted-runtime rlib, strict LLVM linker, host libraries,
   and framework set: PASS. The stubs object contains no generated stubs.
   `simple_mcp_server --help` prints the MCP help and exits0.
   Commands/logs: `relink-mcp.sh`, `mcp-relink/{link,help}.log`.

Relinked MCP SHA256:
`38079330f913abcaef82e11d3bd4c5376aa78b0fdeff0f19cb75da7b6d1e9ad4`.
This is a diagnostic relink, not a new admitted Phase2 artifact. Architecture's
method is dead-stripped from the final executable; its unique definition is
verified in the relocatable object and its behavior in the native fixture.

## Resource evidence and limits

Runtime object decreases from237840 to236232 bytes (1608 bytes).
Changed runtime compile:0.57s,155910144-byte peak child RSS.
Exact green relocatable link:0.02s,7634944-byte peak child RSS.
Native fixture build:2.50s,201216KiB peak sampled process tree; quiescent.
Fixture execution:0.17s,8945664-byte peak child RSS.
Full retained MCP relink:0.13s,106800KiB peak sampled process tree; quiescent.
MCP help:0.34s,9568256-byte peak child RSS. Its short-lived process was missed
by the100ms tree sampler's peak (2544KiB); the child rusage is retained rather
than claiming that sampled peak represents its full maximum.
All supervised commands exited0 under5859375KiB sampled enforcement;
`hard_memory_limit=0`. No performance improvement is claimed from these short
runs. The fix removes code and has no new allocation or synchronization path.

The source-ownership SSpec is added but not executed: the Phase2 full CLI/test
runner is still unavailable. Compiler/lib/MCP/LSP checks, MCP stdio integration,
full Phase2, and bootstrap remain root-owned pending gates. No push performed.
