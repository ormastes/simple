# native-build LLVM lane: 4-layer defect stack fully mapped (seed lane now WORKS with env)

- **Date:** 2026-07-26
- **Lane:** macOS host native-build (default = LLVM backend)
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).

## Working recipe (proven: probe compiles, links, runs)
```
PATH="/opt/homebrew/opt/llvm/bin:$PATH" LIBRARY_PATH=/opt/homebrew/lib \
  src/compiler_rust/target/bootstrap/simple native-build --entry x.spl --output x.bin
```

## The four layers (each masked the next)
1. **Compiled stage4 binary miscompile** (open, keystone): every stage4-compiled binary
   (03:45/13:12/tip vintages) SIGILLs `udf 0xc11f` in `MirToLlvm.llvm_type_text` at its
   first field access — even a source-level `if ty == nil` guard placed before it does
   not fire. The same compiler source INTERPRETED by the seed works — so the pure-Simple
   source is correct and the seed cranelift pipeline MISCOMPILES the type-lowering path
   (suspect: nested-match flattening in `lower_type`). This crash fires BEFORE the llc
   check, so compiled binaries never even report layer 2.
2. **llc discovery** (env workaround): Homebrew LLVM is keg-only; `llc` is not on PATH.
   The compiler probes PATH only → `CompileError(location: nil, message: llc not found)`.
   Fix direction: probe `/opt/homebrew/opt/llvm/bin` (and `llvm@N` kegs) on macOS.
3. **SDL2 link path** (env workaround): default runtime bundle links `-lSDL2` but the
   link command lacks `-L/opt/homebrew/lib` (sdl2-compat provides libSDL2-2.0.dylib
   there). Fix direction: add Homebrew lib dir to the macOS link search path.
4. **CompileError nil-location formatting** (open): the "llc not found" error carries
   `location: nil`; formatting it crashes compiled binaries with the SAME
   "field access on nil receiver" signature as layer 1 — which is why layer 2 was
   invisible for a full day of debugging. Fix: nil-safe error formatting.

## Knock-on effects now explained
- MCP `node_repl` artifact rebuilds all died (layers 1/2/3 in different lanes).
- Cranelift host-lane probe reached linking and failed `cc linking failed` — layer 3
  (SDL2), not a codegen defect. A stray `[DEBUG] 550670556` print sits in that path.
- SimpleOS kernel builds are cranelift/x86_64-none (no llc/SDL2) — unaffected by 2-4;
  their long "timeouts" are the separate single-core-slow-compile issue.
