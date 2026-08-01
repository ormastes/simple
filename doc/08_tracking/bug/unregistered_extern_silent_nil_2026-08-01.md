# An unregistered `@extern fn` is not a link error — it is a silent nil, a silent 0, or a SIGILL (2026-08-01)

**Status:** PARTIALLY FIXED. The live `_cos`/`_sin` instance is fixed and a
detection gate (`scripts/check/check-extern-registration.shs`) now enumerates
the family. The per-lane fall-through sites are located but NOT patched — each
needs a bootstrap rebuild.

**Class:** silent wrong answer. Related:
`game2d_f64_to_i32_extern_unregistered_2026-07-31.md` (same family; commit
`b9ae3d91c07` fixed three of its members and left `_cos`/`_sin` behind).

Base for all transcripts below: `55115a82411`, seed binary
`bin/release/x86_64-unknown-linux-gnu/simple_seed`.

## Proof

```
$ cat r1.spl
@extern fn _totally_bogus_symbol_xyz(a: i64) -> i64
fn main():
    val b = _totally_bogus_symbol_xyz(7)
    print("bogus(7) = {b}")

$ simple_seed run r1.spl
timeout: the monitored command dumped core
rc=132                                    # SIGILL. No symbol name. No link error.
```

```
$ cat r2.spl
extern fn rt_totally_bogus_symbol_xyz(a: i64) -> i64
fn main():
    val b = rt_totally_bogus_symbol_xyz(7)
    print("bogus(7) = {b}")

$ simple_seed run r2.spl
ERROR simple_compiler::interpreter_sffi: rt_interp_call error:
  SemanticWithContext(... "unknown extern function: rt_totally_bogus_symbol_xyz" ...)
bogus(7) = 0
rc=0                                      # logs, then RETURNS 0 AND EXITS CLEAN
```

Even the *declared* `extern fn` form — the one with a "hard error" — is **not
fatal**: it logs and then yields `0` with exit status `0`. `SIMPLE_NO_JIT=1`,
`SIMPLE_JIT=0`, `SIMPLE_INTERP=1` and `SIMPLE_DISABLE_JIT=1` all leave the
`@extern` crash unchanged.

## Root cause: two syntaxes, two code paths

| form | AST node | in `EXTERN_FUNCTIONS` | miss behavior |
|---|---|---|---|
| `extern fn rt_x() -> i64` | `Node::Extern` | yes | logged error, then `0`, exit 0 |
| `@extern fn _cos(x: f64) -> f64` | `Node::Function`, body `vec![]` | **no** | **silent nil / SIGILL** |

`@extern fn` parses as an ordinary bodyless function — the same path as an
abstract method — at
`src/compiler_rust/parser/src/parser_impl/functions.rs:132-152`:

```rust
} else if !self.check(&TokenKind::Colon) {
    // No colon means bodyless declaration (e.g., @extern fn foo() -> T)
    true
```

The `extern` decorator is then explicitly dropped as "a codegen directive, not a
runtime decorator" at
`src/compiler_rust/compiler/src/interpreter_eval.rs:656-670`, and nothing ever
inserts the name into `EXTERN_FUNCTIONS` (that happens only for `Node::Extern`).
The call therefore resolves to a normal user function with zero statements and
falls out of `function_exec.rs` as `Value::Nil`.

## Fall-through sites, per lane

| lane | unregistered extern → | site |
|---|---|---|
| A1 pure-Simple MIR interp | silent `0` | `src/compiler/95.interp/mir_interpreter.spl:285`, `:289`, `:763`; `mir_interp_intrinsics.spl:306` |
| A2 Rust seed, `extern fn rt_*` | logged, then `0`, exit 0 | `interpreter_extern/mod.rs:2568` → `common/error_utils.rs:23` |
| A2 Rust seed, `@extern fn` | **silent `Value::Nil`** | `interpreter_call/core/function_exec.rs:631`, reached because `interpreter_call/mod.rs:266-301` sees `is_extern == false` |
| B Cranelift JIT | errors, then de-JITs whole module into A2 | `codegen/jit.rs:122-161`; on Windows `dlsym_resolves` returns `true` unconditionally (`jit.rs:354-360`), so the guard is inert there |
| C1 seed native link | **weak `return 0` stub** for any non-`rt_` name | `linker/native_binary/stubs.rs:328`; guard filters `starts_with("rt_")` at `:477` |
| C2 freestanding | weak `return 0`, ratcheted | `pipeline/native_project/stubs.rs:758-762`; ratchet `:243` |
| C3 SimpleOS pure-Simple | fabricates via `auto_stubs.c` | `llvm_native_link.spl:1825`, `:2535`; filters `rt_`/`lib__`/`os__` only |

The tree-walking interpreter is **not** correct here — unusually for this repo,
it is one of the wrong lanes.

## Why the existing gate never fired

`scripts/check/check-seed-extern-registry.shs` is the only static check. It
misses this on three independent counts:

1. its regex requires a literal `extern fn` — `@extern fn` never matches;
2. its regex requires an `rt_` prefix — `_cos`, `_sin`, `_f64_to_i32` never match;
3. its scope is `src/compiler` + `src/app` — `src/lib`, `src/os` are never scanned.

It is also a ratchet whose "registered" set is any `rt_*` token appearing
anywhere in `src/compiler_rust`, including inside a comment.

## Fixed in this change

`src/lib/gc_async_mut/game2d/transform.spl` declared:

```simple
# FFI stubs (implemented by the native runtime for f64 trig)
@extern fn _cos(x: f64) -> f64
@extern fn _sin(x: f64) -> f64
```

The comment is false: no such symbol exists in `src/runtime` or
`src/compiler_rust` — the only hits are two Rust *comments*
(`mir/lower/lowering_core.rs:283`, `codegen/instr/basic_ops.rs:224`). Both were
called live at `transform.spl:87-88` to build the rotation matrix, so **every
rotated `Transform2D` produced a garbage world matrix** — the same failure mode
as the `_f64_to_i32` siblings, in the same subsystem.

Replaced with pure-Simple Taylor-series implementations mirroring
`src/lib/skia/entity/matrix.spl`, so behaviour is identical under interpreter,
JIT and native codegen.

Note `src/lib/nogc_sync_mut/gpu/engine3d/types3d.spl:297,300` defines its own
local `fn _sin`/`fn _cos` (f32). Those are real pure-Simple definitions and are
fine — but they are **module-scoped and did not resolve transform.spl's
extern**. Any registration check that counts a same-named `fn` in an unrelated
module as "registered" will produce a false negative here; this one does not.

### Verification (RED then GREEN)

Probe: build a `Transform2D` at rotation `0` and `pi/2`, print `m00`/`m10`.

| | `rot=0` | `rot=pi/2` |
|---|---|---|
| before (unpatched) | *core dumped, 0 lines of output* | *(none)* |
| after (fixed) | `m00=0.9999999999939768 m10=0.0` | `m00=-0.00000077278588942 m10=0.9999999999939768` |

i.e. `cos 0 = 1`, `sin 0 = 0`, `cos pi/2 = 0`, `sin pi/2 = 1`. Spec added at
`test/01_unit/lib/gc_async_mut/game2d/transform_trig_spec.spl`.

**Gate honesty note:** `simple test` delegates to the Rust seed interpreter, so
that spec gates lanes A1/A2 only. It is NOT an active gate on the native/link
path (lanes C1–C3); those remain unguarded by any spec.

## Detection gate added

`scripts/check/check-extern-registration.shs` enumerates all three `@extern`
surface forms across `src/` and `test/` (vendored paths excluded) and reports
every symbol with no registration. Runs in ~3.6 s.

The **sanctioned exemption is the `bare` ABI tag** — `@extern("bare", "sym")` —
which is already how freestanding/baremetal intrinsics are annotated in source
(30 declarations, all under `src/compiler_rust/lib/std/src/bare/`: `mem_*`,
`*_interrupts`, `*_memory_barrier`). That is the only exemption: there is
deliberately no env-var escape hatch, no allowlist file and no stub-emitting
mode, because fabricating a weak nil stub converts a silent nil into a silent
nil with paperwork.

Default mode is report-only (exit 0) because of the backlog below; `--strict`
makes it a hard error and is the intended end state.

The script carries two self-checks, because a detection gate that silently
matches nothing is the same class of defect it exists to catch:
- a **vacuity guard** failing if fewer than 100 declarations are found (~385 expected);
- a **positive control** requiring `rt_file_read_text` to be detected as registered.

Non-vacuity of the gate itself is proven: run against the unpatched tree it
emits
`unregistered_extern=_cos (src/lib/gc_async_mut/game2d/transform.spl:142)` and
`unregistered_extern=_sin (...:143)`, and `--strict` exits 1.

## Current counts

```
extern_decl_total=385
extern_registered=195
extern_bare_exempt=30      (legitimate freestanding class)
extern_unregistered=75     (actionable)
```

## The backlog — 75 unregistered non-`bare` extern symbols

By group:

- **38 in `src/compiler/90.tools/sffi_gen/specs/treesitter.spl`** — *input data*
  to the sffi_gen code generator, not call sites. Expected to be unregistered;
  should be excluded by scope, not by exemption.
- **21 in `src/compiler_rust/lib/std/src/tooling/`** — watch/reload/dashboard
  helpers (`rt_fsevents_*`, `rt_http_*`, `rt_websocket_*`, `rt_dir_entries`,
  `rt_execute_command`).
- **12 in `src/app/interpreter/extern/`** — `ffi_regex_*` (note `sffi_regex_find`
  *does* exist in `runtime/src/value/mod.rs:1012`, so these may be a
  naming-variant mismatch rather than a true gap) and four `rt_math_*`. This
  tree is separately known to be unexercisable by specs.
- **2 in `src/compiler_rust/lib/std/src/spec/snapshot/`**, **1 in `.../io/`**,
  **1 in `.../tooling/core/`**.

Full machine-readable list, `symbol<TAB>file:line`:

<!-- BEGIN unregistered-extern-list -->
```
ffi_regex_captures	src/app/interpreter/extern/regex.spl:22
ffi_regex_find	src/app/interpreter/extern/regex.spl:16
ffi_regex_find_all	src/app/interpreter/extern/regex.spl:19
ffi_regex_is_match	src/app/interpreter/extern/regex.spl:13
ffi_regex_replace	src/app/interpreter/extern/regex.spl:25
ffi_regex_replace_all	src/app/interpreter/extern/regex.spl:28
ffi_regex_split	src/app/interpreter/extern/regex.spl:31
ffi_regex_split_n	src/app/interpreter/extern/regex.spl:34
rt_dir_entries	src/compiler_rust/lib/std/src/tooling/watch/watcher.spl:13
rt_execute_command	src/compiler_rust/lib/std/src/tooling/dashboard/collectors/vcs_collector.spl:81
rt_fsevents_close	src/compiler_rust/lib/std/src/tooling/watch/watcher.spl:420
rt_fsevents_create	src/compiler_rust/lib/std/src/tooling/watch/watcher.spl:414
rt_fsevents_read	src/compiler_rust/lib/std/src/tooling/watch/watcher.spl:417
rt_http_request_path	src/compiler_rust/lib/std/src/tooling/watch/reload.spl:302
rt_http_response_send	src/compiler_rust/lib/std/src/tooling/watch/reload.spl:305
rt_http_server_accept	src/compiler_rust/lib/std/src/tooling/watch/reload.spl:299
rt_http_server_start	src/compiler_rust/lib/std/src/tooling/watch/reload.spl:296
rt_inotify_add_watch	src/compiler_rust/lib/std/src/tooling/watch/watcher.spl:313
rt_inotify_add_watch	src/compiler_rust/lib/std/src/tooling/watch/watcher.spl:358
rt_inotify_close	src/compiler_rust/lib/std/src/tooling/watch/watcher.spl:319
rt_inotify_init	src/compiler_rust/lib/std/src/tooling/watch/watcher.spl:310
rt_inotify_read	src/compiler_rust/lib/std/src/tooling/watch/watcher.spl:316
rt_math_fract	src/app/interpreter/extern/math.spl:171
rt_math_lcm	src/app/interpreter/extern/math.spl:156
rt_math_rem	src/app/interpreter/extern/math.spl:174
rt_math_sign	src/app/interpreter/extern/math.spl:168
rt_module_load	src/compiler_rust/lib/std/src/tooling/watch/reload_apply.spl:168
rt_module_unload	src/compiler_rust/lib/std/src/tooling/watch/reload_apply.spl:145
rt_path_exists	src/compiler_rust/lib/std/src/tooling/generics_migrate.spl:337
rt_path_exists	src/compiler_rust/lib/std/src/tooling/todo_parser.spl:419
rt_reflect_function_name	src/compiler_rust/lib/std/src/spec/snapshot/runner.spl:197
rt_reflect_source_file	src/compiler_rust/lib/std/src/spec/snapshot/runner.spl:185
rt_sha256	src/compiler_rust/lib/std/src/tooling/core/incremental.spl:38
rt_ts_node_child	src/compiler/90.tools/sffi_gen/specs/treesitter.spl:212
rt_ts_node_child_count	src/compiler/90.tools/sffi_gen/specs/treesitter.spl:201
rt_ts_node_end_byte	src/compiler/90.tools/sffi_gen/specs/treesitter.spl:164
rt_ts_node_end_point	src/compiler/90.tools/sffi_gen/specs/treesitter.spl:186
rt_ts_node_has_error	src/compiler/90.tools/sffi_gen/specs/treesitter.spl:317
rt_ts_node_is_extra	src/compiler/90.tools/sffi_gen/specs/treesitter.spl:306
rt_ts_node_is_missing	src/compiler/90.tools/sffi_gen/specs/treesitter.spl:295
rt_ts_node_is_named	src/compiler/90.tools/sffi_gen/specs/treesitter.spl:284
rt_ts_node_is_null	src/compiler/90.tools/sffi_gen/specs/treesitter.spl:328
rt_ts_node_named_child	src/compiler/90.tools/sffi_gen/specs/treesitter.spl:235
rt_ts_node_named_child_count	src/compiler/90.tools/sffi_gen/specs/treesitter.spl:224
rt_ts_node_next_sibling	src/compiler/90.tools/sffi_gen/specs/treesitter.spl:258
rt_ts_node_parent	src/compiler/90.tools/sffi_gen/specs/treesitter.spl:247
rt_ts_node_prev_sibling	src/compiler/90.tools/sffi_gen/specs/treesitter.spl:269
rt_ts_node_start_byte	src/compiler/90.tools/sffi_gen/specs/treesitter.spl:153
rt_ts_node_start_point	src/compiler/90.tools/sffi_gen/specs/treesitter.spl:175
rt_ts_node_symbol	src/compiler/90.tools/sffi_gen/specs/treesitter.spl:142
rt_ts_node_type	src/compiler/90.tools/sffi_gen/specs/treesitter.spl:131
rt_ts_parser_free	src/compiler/90.tools/sffi_gen/specs/treesitter.spl:37
rt_ts_parser_new	src/compiler/90.tools/sffi_gen/specs/treesitter.spl:26
rt_ts_parser_parse	src/compiler/90.tools/sffi_gen/specs/treesitter.spl:61
rt_ts_parser_parse_incremental	src/compiler/90.tools/sffi_gen/specs/treesitter.spl:73
rt_ts_parser_set_language	src/compiler/90.tools/sffi_gen/specs/treesitter.spl:45
rt_ts_query_capture_count	src/compiler/90.tools/sffi_gen/specs/treesitter.spl:377
rt_ts_query_capture_name	src/compiler/90.tools/sffi_gen/specs/treesitter.spl:388
rt_ts_query_cursor_exec	src/compiler/90.tools/sffi_gen/specs/treesitter.spl:420
rt_ts_query_cursor_free	src/compiler/90.tools/sffi_gen/specs/treesitter.spl:412
rt_ts_query_cursor_new	src/compiler/90.tools/sffi_gen/specs/treesitter.spl:404
rt_ts_query_cursor_next_capture	src/compiler/90.tools/sffi_gen/specs/treesitter.spl:441
rt_ts_query_cursor_next_match	src/compiler/90.tools/sffi_gen/specs/treesitter.spl:430
rt_ts_query_cursor_set_byte_range	src/compiler/90.tools/sffi_gen/specs/treesitter.spl:452
rt_ts_query_cursor_set_point_range	src/compiler/90.tools/sffi_gen/specs/treesitter.spl:462
rt_ts_query_free	src/compiler/90.tools/sffi_gen/specs/treesitter.spl:358
rt_ts_query_new	src/compiler/90.tools/sffi_gen/specs/treesitter.spl:343
rt_ts_query_pattern_count	src/compiler/90.tools/sffi_gen/specs/treesitter.spl:366
rt_ts_tree_edit	src/compiler/90.tools/sffi_gen/specs/treesitter.spl:109
rt_ts_tree_free	src/compiler/90.tools/sffi_gen/specs/treesitter.spl:90
rt_ts_tree_root_node	src/compiler/90.tools/sffi_gen/specs/treesitter.spl:98
rt_walk_directory	src/compiler_rust/lib/std/src/io/fs_helpers.spl:71
rt_walk_directory	src/compiler_rust/lib/std/src/tooling/generics_migrate.spl:357
rt_walk_directory	src/compiler_rust/lib/std/src/tooling/todo_parser.spl:427
rt_websocket_send	src/compiler_rust/lib/std/src/tooling/watch/reload.spl:383
```
<!-- END unregistered-extern-list -->

## Caveats on the list

The "registered" set is still a superset — a symbol counts as registered if it
appears as `sym(` or `"sym"` in non-comment C/H/Rust, or as a quoted string in a
`.spl` registration table. So **75 is a lower bound**. Any layer doing prefix
rewriting (`ffi_` → `sffi_`) would also produce false positives here.

Comments are excluded, which matters: an earlier revision of this scan counted
`_sin` as registered purely on the strength of a Rust doc comment, and so missed
the very bug that motivated the work.

## Remaining work

1. Patch the per-lane fall-throughs so an unregistered `@extern` aborts with the
   symbol name instead of yielding nil/0/SIGILL. The cheapest correct fix is to
   register `@extern`-decorated names into `EXTERN_FUNCTIONS` alongside
   `Node::Extern` so the existing `unknown extern function` path fires — but
   note that path currently only *logs*, so it must be made fatal too. Needs a
   bootstrap rebuild.
2. Narrow the gate's scope to exclude sffi_gen generator inputs, resolve the
   `ffi_`/`sffi_` naming question, then flip it to `--strict` in the pre-push
   guards.
3. Close the `rt_`-prefix hole in the native stub guards (`stubs.rs:477`,
   `llvm_native_link.spl:1825`) — a non-`rt_` symbol is silently given a weak
   `return 0` body today.
