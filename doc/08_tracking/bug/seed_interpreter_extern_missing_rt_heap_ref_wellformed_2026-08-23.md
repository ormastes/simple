# `native-build` of hello world dead: seed interpreter_extern table missing `rt_heap_ref_wellformed` (2026-08-23)

Status: **FIXED** (adapter added, verified by running). Two related defects
found in the same investigation remain **OPEN** — see §4 and §5.

## 1. Symptom

On `origin/main` at `c1efb59cf09`, with a seed built *from that exact tree*:

```
$ bin/simple native-build --backend=llvm --entry hello.spl -o hello_simple
error: semantic: unknown extern function: rt_heap_ref_wellformed
error: native-build worker exited with code 1.
rc=1
```

`hello.spl` is three lines and imports nothing. **Every** host native-build was
dead, not just this fixture. This is the same hole
`doc/10_metrics/startup/cross_language_startup_benchmark_2026-08-18.md` recorded
as "`bin/simple native-build hello.spl` **fails** on the seed … so no Simple
compiled-binary lane could be measured" — that doc could not name the cause.

Ruled out first: a **stale** deployed binary. The initially-deployed seed
genuinely predated the symbol (`strings bin/simple | grep -c
rt_heap_ref_wellformed` = 0). A fresh `cargo build --release --bin simple` from
`c1efb59cf09` reported 8 hits and **still failed identically** — so the defect is
in the tree, not the artifact.

## 2. Root cause — a split-registry gap

`rt_heap_ref_wellformed` is defined and registered on every lane EXCEPT the one
the native-build worker actually uses:

| lane | status |
|---|---|
| C runtime `src/runtime/runtime_native.c:7441` | defined |
| C header `src/runtime/runtime.h:587` | declared |
| Simple core `src/runtime/simple_core/core_enum.spl:73` | defined |
| Rust runtime `src/compiler_rust/runtime/src/value/objects.rs:395` | `pub extern "C" fn` |
| Codegen/link registry `src/compiler_rust/common/src/runtime_symbols.rs:663` | registered |
| **Seed interpreter dispatch `src/compiler_rust/compiler/src/interpreter_extern/`** | **ABSENT** |

`bin/simple native-build` spawns a worker that runs the pure-Simple compiler
**under the seed's interpreter**. That worker interprets
`src/compiler/80.driver/driver_hir_pipeline_lowering.spl`, which declares
(`:55`) and calls (`:142`, `:505`) `rt_heap_ref_wellformed`. Interpreted extern
calls resolve through `interpreter_extern/mod.rs`, a table **separate** from
`runtime_symbols.rs`, and nothing keeps the two in sync.

## 3. Fix

`compiler/src/interpreter_extern/sffi_value.rs` gains
`rt_heap_ref_wellformed_fn`, registered in `interpreter_extern/mod.rs` next to
its nearest sibling `rt_value_is_heap`.

Semantics are deliberately **not** a copy of `rt_value_is_heap_fn`. The .spl
declaration is `(value: Any) -> bool` and real call sites pass class instances
(`self.ctx.module_surfaces.unwrap()`), so an `.as_int()?` adapter would have
traded "unknown extern" for a mid-build type error. `objects.rs:389-393`
documents the contract as FORMATION ONLY and "can never false-reject a live
object", so:

* `Value::Nil` -> `false`
* `Value::Int(raw)` -> delegate to the real runtime probe on the raw carrier, so
  a scalar payload still reports 0 exactly as documented
* anything else -> `true`; the interpreter has no unformed heap object

## 4. OPEN — the defect CLASS, not just this symbol

This is not a one-off. `/usr/bin/grep -rn "unknown extern function"
src/lib/` returns a documented history of the identical failure for `rt_slice`,
`rt_sdl2_init`, `rt_winit_event_loop_new`, `rt_opengl_init`, `rt_image_load`,
`rt_webgpu_create_device`, `rt_screenshot_enable`, `rt_socket_set_nonblocking`,
`rt_io_file_*`. **There is no parity gate** between `interpreter_extern/mod.rs`
and either `runtime_symbols.rs` or the set of `extern fn rt_*` declarations in
`src/**/*.spl`, so the next such gap is found only when something dies.

TODO(seed-extern-parity): add a fail-closed check that every `extern fn rt_*`
reachable from the compiler's own sources has an `interpreter_extern` entry, in
the style of `scripts/check/check-unbacked-extern-ratchet.shs`. Not built here —
naming it, not deferring it silently.

## 5. OPEN — second blocker found immediately downstream

With the fix in place, `hello.spl` builds and runs. A **trivial-import**
fixture (`use std.common.text.{trim}`) still fails:

```
error: MIR lowering error: unresolved method call: index_of
```

so the "Simple native binary, one stdlib import" benchmark row remains
unmeasurable. Separate defect (MIR lowering, not extern dispatch); recorded here
rather than dropped.

## 6. Reproduce / verify

```sh
git worktree add --detach <wt> c1efb59cf09
cd <wt>/src/compiler_rust && cargo build --release --bin simple   # pre-fix -> FAILS below
cd <wt> && bin/simple native-build --backend=llvm --entry hello.spl -o hello_simple
```

Post-fix, measured 2026-08-23 09:02, load average 35.3/33.8/32.5:
`rc=0`, `hello_simple` = 22,264 bytes, prints `hello`, dynamically linked
against libc only. Startup numbers in
`doc/10_metrics/startup/cross_language_startup_benchmark_2026-08-18.md` §2026-08-23.
