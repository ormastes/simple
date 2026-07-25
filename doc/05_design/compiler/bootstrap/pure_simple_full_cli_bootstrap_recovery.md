# Pure-Simple full CLI bootstrap recovery — detail design

Date: 2026-07-17

## Invariants

1. Rust seed remains bootstrap-only; normal tools require an admitted
   pure-Simple full CLI.
2. LLVM and native codegen reject unresolved symbols.
3. MIR block lowering emits no statement after an explicit terminator.
4. Native object staging survives unrelated system-temp cleanup and concurrent
   cache `--clean`.
5. Each build has a unique staging directory; cached objects keep their current
   content-addressed ownership.

## Changes

- Normalize the seven invalid source/frontend shapes exposed by LLVM.
- Make `ArrayBuilder` use the existing typed runtime capacity boundary and
  keep logical length and advertised capacity consistent.
- Stop pure-Simple MIR block lowering after an explicit terminator.
- Route qualified `Dict` builtins before ordinary method lookup.
- Create native object staging under the cache parent, not system temp or the
  recursively cleaned cache directory.

No new public abstraction, cache format, WebIR/DrawIR path, or font-rendering
path is introduced.

## Verification order

1. Focused Rust regressions for Dict dispatch and staging lifetime.
2. Focused Simple specs for CUDA rejection, dead-after-return MIR, and
   ArrayBuilder/Tensor behavior using an admitted pure-Simple runner.
3. Source checks for compiler/lib/MCP/LSP.
4. Cache-preserving Stage 2 shard, then full CLI build once heavy-work preflight
   permits it.
5. Redeploy/tool smoke and existing font/SimpleOS/native-GPU evidence gates.
