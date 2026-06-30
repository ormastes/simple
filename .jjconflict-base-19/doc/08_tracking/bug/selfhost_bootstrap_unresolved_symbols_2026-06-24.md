# Self-host bootstrap broken: stage4 (seed-built) has 548 unresolved symbols

**Date:** 2026-06-24
**Area:** bootstrap / self-hosting / native-build (cranelift) codegen
**Severity:** blocker for deploying the pure-Simple compiler as `bin/simple`
(which is what would make `compile --target wasm32` use pure-Simple `compile_to_wasm`).

## Chain of failure (current, reproduced via `bootstrap-from-scratch.sh --pure-simple`)
1. **Stage 3 (self-host) fails:** `bootstrap_main.spl`'s `run_native_build_bootstrap`
   is a deliberate STUB (`src/app/cli/bootstrap_main.spl:24-27`) that prints
   "bootstrap_main cannot emit a seed-wrapper fallback … rebuild with the full
   Simple driver" and exits 1. So the stage2 binary (compiled from the *minimal*
   `bootstrap_main.spl`) cannot native-build → Stage 3 self-host verification fails.
2. **Stage 4 falls back to the SEED:** because Stage 3 failed, Stage 4 compiles the
   full `src/app/cli/main.spl` with the **Rust seed** (cranelift), not the Simple
   compiler.
3. **The seed can't fully compile the full Simple compiler:** the stage4
   native-build reports **"Generating 548 stub functions for unresolved symbols"**.
   Clusters: `<module>__ParserModule` (×32+), SPIR-V `builder_emit_*`/`builder_*`
   (×24), `Jit*` classes, libc termios (`cfgetispeed@GLIBC` …), and core primitives
   (`Dict`, `alloc`, `chars_len`, `args_len`, `code_len`), plus `BidirHirExpr.*`
   methods. (Preview truncated; 548 total.)
4. **Resulting stage4 is functionally broken:** it compiles a trivial program to
   SMF, but `compile <file> --target wasm32` reports **"Source file not found"**
   for a file that exists — the `--target`-present arg-parse path hits a stubbed
   symbol and mis-assigns `source_file` (the error is from the early
   `file_exists` check at `cli_compile_part1.spl:446`, before the wasm dispatch
   at :495). The non-wasm compile path reads files fine.

## Why this matters
The pure-Simple wasm path (`CompilerDriver.compile_to_wasm` → `WasmCodegenAdapter`,
`driver.spl:693`) WORKS in interpreter/test mode (`wasm_compile_spec` 37/37,
`wasm_e2e_spec` 4/4). It only runs when the **self-hosted** binary is deployed.
The self-hosted binary can't be produced cleanly because of the above.

## Dominant cluster root cause: `use X as Y` alias mangling (seed codegen)
`ParserModule` (32+ unresolved) is an **import alias**:
`use compiler.frontend.parser_types.{Module as ParserModule, ...}`
(`_Items/lowering_helpers.spl:10`). The seed's native-build mangles method symbols on the
*alias* (`<using_module>__ParserModule`) instead of the canonical type
(`parser_types.Module`), so call sites don't match definitions → unresolved. This
is why "most cases work" — only `use X as Y`-aliased types break. (Other clusters
— SPIR-V `builder_*`, `Jit*`, core primitives — are separate gaps.)

## The catch-22 (important)
Stage 4 is built **by the Rust seed**, so these unresolved symbols come from the
**seed's** native codegen. Fixing them means fixing the **Rust seed's** codegen —
which is exactly the Rust-layer work the project philosophy ("pure Simple is main,
Rust is just seed") wants to avoid. But the self-hosted Simple compiler can't fix
its own bootstrap (chicken-and-egg): to produce a clean self-hosted `bin/simple`,
the seed must first compile the full Simple compiler correctly. So "fix the
self-host bootstrap" *inherently* requires Rust-seed codegen fixes.

The pure-Simple wasm codegen (`compile_to_wasm`) is NOT the problem — it works in
interpreter/test mode (41 tests). The blocker is purely deploying it as a native
binary, which the seed currently can't build correctly.

## Scope
This is NOT a single fix. It requires either:
- (A) Making the seed's cranelift native-build resolve the 548 symbols so it can
  fully compile the Simple compiler (deep Rust-seed codegen work — the diverse
  clusters suggest multiple distinct resolution gaps), OR
- (B) Bootstrapping stage2/3 from the **full** driver so the Simple compiler (not
  the seed) builds stage4 — but the seed still has to compile the full driver
  once, hitting the same 548 gaps.

## 2026-06-24 progress — "seed delegates to pure-Simple interpreter" path
Goal: make `bin/simple run src/compiler/80.driver/main.spl compile … --target wasm32`
work so the seed can delegate wasm to the (working) pure-Simple `compile_to_wasm`.

**FIXED — run-mode trap on the compiler driver:** the driver pulled the heavy
`app.io.mod` hub via `driver/main.spl` (`use app.io.mod (rt_debug_stack_trace_lines)`,
used only by a DEAD `format_runtime_error_message`) and `project.spl`
(`use app.io.{file_read}`). Decoupled both (removed the dead fn + import; switched
`file_read` to `std.nogc_sync_mut.io.file_ops`). Now `bin/simple run
.../80.driver/main.spl` reaches and runs `main()` (was silently skipped before).
Both files `check` OK. (Same anti-pattern/fix as the MCP source-mode fix.)

## 2026-06-24 (cont.) — FIXED a real bug: `driver.spl` shadowed by `driver/` dir
Loader trace (`SIMPLE_LOADER_TRACE=1`) showed the interpreter never loaded
`80.driver/driver.spl` (the `CompilerDriver` class + `compiler_driver_create`):
a `driver.spl` FILE and a `driver/` DIRECTORY both existed under `80.driver/`, so
the loader `init-redirect`ed the module name to `driver/__init__.spl`, shadowing
the file; that `__init__` then re-exported `compiler.driver.driver` which looped
back to itself (`circular: … returning partial`) → `compiler_driver_create not
found` at interpreter runtime. (Native hides this — it compiles every .spl by
path.) **Fix:** renamed the dir `80.driver/driver/` → `80.driver/driver_build/`
(it only held `incremental.spl`/`parallel.spl`), repointed the 2 importers
(`driver_aot_output.spl`), dropped the dir-init's now-needless `CompilerDriver`
re-export. Verified: `compiler_driver_create not found` is GONE; `cli/check.spl`
(real driver consumer) checks OK; `wasm_e2e_spec` 4/4 (no regression).

**REMAINING blocker — silent run-mode large-graph trap:** with `driver.spl` now
loading, `bin/simple run .../80.driver/main.spl` loads the full compiler-driver
graph (~9s) then exits 1 **before `main()` runs**, with NO surfaced error (not the
`MAX_TOTAL_MODULES`=800 cap; no E-code/panic even at `RUST_LOG=warn`). This is the
same silent swallowed-load-`Err` trap that originally hid behind `app.io.mod`
(MCP) — the interpreter aborts loading a very large module graph without
reporting why. Pinning it needs instrumenting the Rust seed interpreter's module
loader/evaluator (a seed rebuild to iterate) — the deep Rust-layer work. The two
pure-Simple fixes above are correct progress but the fundamental interpreter trap
remains.

Loader-trace detail (post-collision-fix): `driver.spl` NOW loads
(`loaded: …/80.driver/driver.spl (7681 exports, 2933ms)`), 574 modules total
(< 800 cap), `compiler_driver_create not found` gone — but `main()` is still not
invoked afterward (rc=1, no `[boot]`, no surfaced error). The trace also shows the
`src/compiler/driver -> 80.driver` SYMLINK yields a dual resolution path:
`circular: …/compiler/driver/driver.spl (returning partial)` (same file reached as
both `compiler/80.driver/driver.spl` and `compiler/driver/driver.spl`). Net: the
interpreter loads the full driver graph then silently declines to run the entry's
`main()` — the deep run-mode trap, likely needing Rust-seed instrumentation to
root-cause.

## 2026-06-24 (cont.) — RESOLVED: the run-mode "main not invoked" trap
Pinned via Rust-seed interpreter instrumentation and FIXED (pushed, origin
`201372604ea`, seed `interpreter_eval.rs`). It was NOT "main never invoked" —
the interpreter was running the **wrong** `main`.

Root cause: `evaluate_module_impl` registers the entry's `fn main` in its first
pass, but the second pass merges lazily-loaded imported modules' functions into
the flat `functions: HashMap<String, FunctionDef>` (last-write-wins). The
pipeline flattener strips imported `main` (`strip_flattened_import_nodes`), but
the lazy second-pass merge does NOT, so when the import graph is large enough to
trigger lazy loads, an imported module's `fn main` clobbers the entry's. The
program then ran an unrelated `main` (no output, exit code of that function) —
indistinguishable from "main not invoked".

Evidence (instrumented seed, `SIMPLE_DEBUG_MAIN=1`): a probe entry with
`use compiler.backend.*` + a trivial `main` had `main_overloads=13`,
`has_main_fn=true`, "invoking main() now", yet returned exit 1 with no output.
`use compiler.frontend.*` (smaller, 71 modules) had `main_overloads=1` and ran
correctly. The trap reproduced with backend AND driver graphs (≥ a few hundred
modules), not with small graphs — confirming it is import-graph driven, not
symlink- or content-specific.

Fix: capture the entry module's `main` right after the first pass (before the
merge) and invoke that; fall back to the flat map for entries with no own `main`.
Verified: backend/driver probes now exit 0 and print; no-import, std-import, and
real app `check`s pass; no interpreter regression (the 186 `cargo test` lib
failures are pre-existing codegen/LLVM/native + filesystem-layout path-resolution
tests, none touching main-selection).

**New downstream blocker (separate, pure-Simple):** with `main` now running, the
driver proceeds through real compile phases and fails in its own frontend bridge
with `error: semantic: class \`Module\` has no field named \`imports\``
(`parser_types.Module` accessed via a non-existent `.imports` field) — a genuine
self-hosted-compiler bug, related to the `ParserModule` alias cluster above.
This is the next thing to fix toward `run`-driving the pure-Simple wasm path.

## 2026-06-24 (cont.) — FIXED next blocker: `Module` struct-name collision
With `main()` now running, the driver hit `error: semantic: class `Module` has
no field named `imports`` at `parser_module_new`. Root cause: two `struct Module`
— the flat `ast.Module {name, items}` and the rich `parser_types.Module {name,
imports, exports, functions, ...}` — collided in the interpreter's global
bare-name struct registry (last-write-wins), so the rich constructor inside
`parser_module_new` built the flat shape. FIXED (pushed, origin `f8ca83a68c8`)
by renaming the flat one to `AstModule` and updating its 4 consumers
(`type_system/checker`, `type_system/module_check`, `monomorphize/partition`,
`module_resolver/manifest` — all use `.items`); `parser_types.Module` stays the
canonical re-exported frontend `Module`. Verified (interpreter, pure-.spl, no
rebuild): `bin/simple run .../80.driver/main.spl --check <file>` runs to
completion (`built frontend module` -> `parsed module`, exit 0); all 5 edited
files `check` OK.

Next blockers toward run-driving the pure-Simple wasm path (separate): the
driver `main.spl` arg parser does not accept `--target` (`Error: unknown option
--target`) — needs `--target wasm32` wired to the backend; and `--check` returns
exit 0 even when it prints a diagnostic.

## Notes
- `bootstrap-from-scratch.sh` only probes the macOS LLVM path
  (`/opt/homebrew/opt/llvm@18`); on Linux it silently uses cranelift even though
  `/usr/lib/llvm-18` is present. (Separate, minor.)
- Interim wasm CLI capability is available by building the seed with
  `cargo +nightly --features wasm-wasi` (LLVM path) — see
  `wasm_cli_emit_no_artifact_2026-05-30.md` — but that is the Rust seed, not the
  pure-Simple compiler.
