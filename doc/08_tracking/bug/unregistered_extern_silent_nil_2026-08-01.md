# An unregistered `@extern fn` is not a link error — it is a silent nil, a silent 0, or a SIGILL (2026-08-01)

**Status:** PARTIALLY FIXED. The live `_cos`/`_sin` instance is fixed, a
detection gate (`scripts/check/check-extern-registration.shs`) enumerates the
family, and as of the update below the JIT fall-through now **warns by
default** and can be made fatal on demand. The individual unbacked symbols are
still unbacked.

> **Update 2026-08-01 (later lane) — the fall-through is no longer silent.**
> `interp_call_handler` swallowed *every* extern error into
> `RuntimeValue::NIL` and exited 0. It now distinguishes "no implementation
> exists" from a real error inside a backed extern and reports the former.
> Default is **warn-only** (values and exit codes unchanged);
> `SIMPLE_STRICT_EXTERN=1` makes it fatal. See "Loud diagnostic" below.

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
extern_decl_total=137
extern_registered=31
extern_bare_exempt=30      (legitimate freestanding class)
extern_unregistered=4      (actionable)
```

## The backlog — 4 unregistered non-`bare` extern symbols remaining

By group:

- ~~**38 in `src/compiler/90.tools/sffi_gen/specs/treesitter.spl`**~~ — **RETIRED
  2026-08-01 by deleting the file.** The original hypothesis here was that these
  were live *input data* to the sffi_gen code generator and so should be excluded
  by scope. That hypothesis is disproved. Evidence:
  1. `TreesitterFFI` is referenced nowhere outside its own file.
  2. `treesitter` is **not** exported from `sffi_gen/specs/__init__.spl`, which
     indexes the 15 spec modules the generator actually consumes.
  3. It was the **only** one of the 48 files in `specs/` to use `@extern` at all;
     every real spec instead declares `fn <name>_specs() -> [InternFnSpec]` and
     builds `InternFnSpec(...)` values. The generator has no `@extern`-class
     reader, and its `@sffi_spec` marker is referenced nowhere.
  4. `rt_ts_*` appears in the Rust tree exactly once, in a `//!` doc comment in
     `interpreter_extern/dynamic_sffi.rs:10` — i.e. never registered. (This is
     precisely the comment-match trap the gate strips for.)
  5. The shipping tree-sitter support is hand-written **pure Simple** under
     `src/compiler/10.frontend/treesitter/` and uses zero `rt_ts_` externs.
  6. Its own header comment pointed at `src/app/sffi_gen/specs/treesitter.spl`,
     a path that no longer exists.

  So it was an abandoned alternative binding approach, never wired to anything —
  dead code, deleted per the repo's no-unused-code rule rather than exempted.
- ~~**16 in `src/compiler_rust/lib/std/src/tooling/watch/`**~~ — **RETIRED
  2026-08-01 by deleting the `watch/` subpackage** (`watcher.spl`, `reload.spl`,
  `reload_apply.spl`, `__init__.spl`) and the two re-export lines it fed in
  `tooling/__init__.spl`. It was a dead second copy of the file watcher:
  1. Zero importers outside its own directory. The only references were
     `tooling/__init__.spl:39,41`, and nothing imports the `std.tooling` root.
  2. `WatchConfig` and `FileChange` *do* appear elsewhere, but resolve to
     unrelated modules: `struct WatchConfig` is defined in
     `src/app/watch/runner.spl:13`, `struct FileChange` in
     `src/app/jj/status.spl:9`. Module-scoped resolution means those are
     name collisions, not consumers — the same trap that made a same-named
     `fn _cos` look like a definition for `transform.spl`'s extern.
  3. The live watcher is `src/app/watch/watcher.spl` (consumed by
     `src/compiler/80.driver/watcher/watcher_daemon.spl:24`,
     `src/app/watch/runner.spl:6`, `src/app/io/_CliCommands/*`), and it uses
     only registered symbols (`rt_file_exists`, `rt_dir_walk`).
  4. Every one of the 16 was a genuine no-implementation gap — inotify, FSEvents,
     HTTP server, websocket, dynamic module load exist in no runtime — so the
     alternative was building whole subsystems for code nothing imports.

  Worth recording, because it is the defect this whole bug is about: the dead
  copy's error handling could not have caught the failure either. Every guard
  tests `< 0` (`watcher.spl:325` `inotify_fd < 0`, `:359` `wd < 0`, `:428`
  `fsevents_handle < 0`, `reload.spl:309`, `:314`), but an unregistered extern
  yields a silent `0`, which is not `< 0`. So the polling fallback would never
  have triggered and the watcher would have run on a bogus fd — and the polling
  path was equally dead, since `rt_dir_entries` and `rt_file_mtime` are
  unregistered too.
- **1 remaining in `src/compiler_rust/lib/std/src/tooling/dashboard/`** —
  `rt_execute_command` (a registered `rt_process_run` equivalent exists at
  `runtime/src/value/sffi/env_process.rs:547`).
- ~~**12 in `src/app/interpreter/extern/`**~~ — **RETIRED 2026-08-01 by deleting
  the `src/app/interpreter/extern/` package (25 files, 178 `@extern` decls).**
  The package is dead code, and the tree says so itself:
  1. `src/app/__init__.spl:33` — "`app.interpreter` - REMOVED. Use
     `core.interpreter` instead"; `compiler/10.frontend/core/interpreter/mod.spl:21`
     — "Legacy Interpreter (DELETED 2026-02-10) … Location: src/app/interpreter/
     (removed)". Both tombstones were written; the files were never deleted.
  2. Zero importers of `app.interpreter.extern[.*]` anywhere in `src/` or `test/`
     outside the package itself, and no `FILE.md` manifest references it.
  3. No spec exercises it; it is not reachable from `interpreter/main.spl`, which
     imports only `core`, `parser`, `ast_convert`.
  4. `ffi/__init__.spl:7`'s `from extern import {load_library, resolve_symbol,
     ExternLib}` resolves to the **sibling** `ffi/extern.spl` (which exports
     exactly those names at `:7`), *not* to this package — so nothing broke.

  On the `ffi_`/`sffi_` naming-mismatch hypothesis: it was correct as far as it
  went. All 8 stems do exist as `sffi_regex_*` with real implementations
  (`runtime/src/value/sffi/regex.rs:92,112,148,189,234,263,296,332`, registered at
  `interpreter_extern/mod.rs:285-292`), and a live wrapper with byte-identical
  signatures already ships at `src/lib/nogc_sync_mut/io/regex_simple.spl:15-22`.
  Re-registering would therefore have produced a second, unreachable copy of a
  binding that already works — so the dead package was deleted instead.
  The four `rt_math_lcm/sign/fract/rem` had no implementation anywhere and no
  caller; they went with it. Deleted, not tagged `bare`: they are ordinary host
  math, not freestanding intrinsics, and `bare` is not a parking space.

  Note this deletion drops `extern_decl_total` from 347 to 169 and
  `extern_registered` from 195 to 33 — the registered figure is an intersection
  with the declared-candidate set, so removing 178 mostly-registered candidates
  necessarily shrinks it. The vacuity guard (bound 100) still passes at 169 and
  was re-checked, not adjusted.
- **2 in `src/compiler_rust/lib/std/src/spec/snapshot/`**, **1 in `.../tooling/core/`**.
- ~~`rt_path_exists` x2, `rt_walk_directory` x3~~ — **RETIRED 2026-08-01 in pure
  Simple, no new runtime symbols.**
  - `rt_walk_directory` (`io/fs_helpers.spl:71`, `tooling/todo_parser.spl:427`,
    `tooling/generics_migrate.spl:357`) was registered in no runtime, so
    `walk_directory` returned a silent nil on *every* call. This was live:
    `io.fs_helpers.walk_directory` is imported by
    `tooling/dashboard/collectors/{spipe,plan}_collector.spl` among others, and
    `generics_migrate.collect_spl_files` saw no files at all.
    `infra.file_io` already exposes `walk_dir_unsafe`, a wrapper over the
    **registered** `rt_dir_walk` (`runtime/src/value/sffi/file_io/directory.rs:223`).
    `fs_helpers.walk_directory` now calls it and applies the include/exclude
    globs in pure Simple (`**`, `*`, `?`), matching the previous contract; the
    two tooling copies import it instead of redeclaring the extern.
  - `rt_path_exists` (`tooling/todo_parser.spl:419`,
    `tooling/generics_migrate.spl:337`) backed a local `fn exist` that had **no
    callers** in either file and was exported from neither. Deleted rather than
    re-pointed at the registered `rt_file_exists`, per the no-unused-code rule.

  Evidence lane: seed `lint` (tree-walking parser, lane A) before vs after, same
  binary and inputs. `todo_parser` and `generics_migrate` sat at `PARSE001` both
  before and after (1 error -> 1 error): pre-existing, untouched by this change.
  `fs_helpers` went from **4 errors including `PARSE001`** to **3 errors with no
  `PARSE001`** -- the remaining three are pre-existing `primitive_api` style
  errors, line-shifted by one added import. No native/link-lane evidence is
  claimed: no working compiler front-end is available in this environment (a
  known-good control file failed to compile, so that check was discarded rather
  than reported as a pass).

Full machine-readable list, `symbol<TAB>file:line`:

<!-- BEGIN unregistered-extern-list -->
```
rt_execute_command	src/compiler_rust/lib/std/src/tooling/dashboard/collectors/vcs_collector.spl:81
rt_reflect_function_name	src/compiler_rust/lib/std/src/spec/snapshot/runner.spl:197
rt_reflect_source_file	src/compiler_rust/lib/std/src/spec/snapshot/runner.spl:185
rt_sha256	src/compiler_rust/lib/std/src/tooling/core/incremental.spl:38
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

## Loud diagnostic (2026-08-01, later lane)

### Where the silence actually was — PROVED, and narrower than assumed

Re-measured at `29992868d68` with a debug seed built from that exact tip. Probe:
a `extern fn totally_nonexistent_ghost_symbol_xyz(a: i64) -> i64` that is called
and printed.

| path | result | loud? |
|---|---|---|
| `compile --native` | `error: codegen: undefined symbol: <name>`, rc=1 | **yes** |
| `native-build` | worker exits 1 | **yes** |
| `run` with `SIMPLE_EXECUTION_MODE=interpreter` | `error: semantic: unknown extern function: <name>`, rc=1 | **yes** |
| `run` (default = JIT) | prints `ghost returned: 3`, **rc=0** | **NO** |

So the surviving silent path is **the JIT only** — not the native link. `3` is
`NIL_VALUE`; it prints as an ordinary integer, which is exactly why this reads
as a legitimate `0`-ish answer. The earlier claim in this file that the native
link weak-stubs any non-`rt_` name did **not** reproduce on either native path
at this tip: both refuse. (The weak-stub fabricator in
`pipeline/native_project/stubs.rs` is still real, but it is reached by the
freestanding/bootstrap configurations, which have their own ratchet, not by a
plain hosted `compile --native`.)

### Root cause (exact line)

`src/compiler_rust/compiler/src/interpreter_sffi.rs`, `interp_call_handler`:
the terminal `Err(e) => { tracing::error!(...); RuntimeValue::NIL }` arm
swallowed **every** extern failure into nil and let the process exit 0. The
`tracing::error!` is not a gate — it does not change the value or the status.

### Fix shipped

`interp_call_handler` now sets a thread-local when a name reaches the terminal
"not found" branch, so the error arm can tell an **unbacked extern** apart from
a genuine error raised *inside* a backed extern. Only the former is reported.

- **default:** one warning per distinct name per process, naming the symbol,
  the arg count, and the fact that nil was substituted. Return value and exit
  status are **unchanged** — this is warn-only on purpose.
- `SIMPLE_STRICT_EXTERN=1`: fail cleanly (diagnostic on stderr, exit 1 -- NOT `abort()`/SIGABRT/core dump) instead of substituting nil. Changed 2026-08-18: it used to `std::process::abort()`, which produced exit 134 and "dumped core" for a fully-diagnosed refusal.
- `SIMPLE_QUIET_EXTERN_WARN=1`: silence the warning without changing any value.

Deliberately **not** promoted to fatal by default: ~919 symbols are unbacked on
the high-confidence count below, and some callers read the nil as "feature
unavailable". Promotion needs its own lane with the fallout measured first.

### Non-vacuity (PROVED)

Control = the *same* source tree at the *same* tip with only
`interpreter_sffi.rs` reverted to its pristine blob, rebuilt with the same
command. Control: no warning, rc=0, `ghost returned: 3`, and
`SIMPLE_STRICT_EXTERN=1` has **zero** effect. Fixed: warning present; strict
mode aborts (rc=134). The delta is attributable to the change, not to drift.
(As of 2026-08-18 strict mode exits 1 cleanly instead of aborting; re-measured
on the fixture `lane_definitely_absent_probe`: default rc=0 `got 3` + warning,
strict rc=1 with the `error: extern ... refuses to substitute nil` line and no
core dump.)

### Measured fallout of the warning — 0

Corpus: every 15th `.spl` under `examples/` and `test/`, first 220 files, run as
`simple run <file>` with the fixed debug seed, 12s timeout each.

```
files run                       220
exit 0                          149
exit 1                           50
timeout (124)                    19
exit 101                          2
warning lines emitted             0
distinct externs warned about     0
```

**Zero.** Not one of the ~919 statically-unbacked symbols was actually *called*
in 220 real programs. The measurement is not vacuous: the same binary emits the
warning for the `ghost` probe above, so the detector demonstrably fires.

Read this carefully — it does **not** say the backlog is harmless. It says the
unbacked declarations are overwhelmingly *unreached* on this corpus, which is
consistent with most of them being dead declarations (disposition: delete) or
reachable only under configurations this corpus never enters (baremetal, T32,
vscode, GPU). It also means the warning is cheap: turning it on by default cost
0 lines of noise across 220 programs.

220 of ~21k `.spl` files is a sample, not a census, so this is **not** grounds
to promote the warning to fatal on its own. A promotion lane should re-run this
over the full corpus and over the spec suite first.

## Counting correction — beware the `insert_simple!` registry

A triage pass that looked only for Rust `extern "C" fn NAME` definitions
classified 1,418 names as unbacked. **109 of those are in fact registered**, via
`insert_simple!("name", path::to::fn)` in
`src/compiler_rust/compiler/src/interpreter_extern/mod.rs` (1,572 such
registrations; 1,422 distinct quoted names). The whole `rt_jit_*` family — one
of the highest-blast-radius groups by declaring-file count — is registered this
way and is **not** a defect. Any future scan that ignores this registry will
manufacture false positives.

Intersecting the two independent methods (this file's
`check-extern-registration.shs`, which does see the registry, and the
definition-scan above) gives **919 unique symbols both agree are unbacked** —
treat that as the actionable core, not 1,418 and not 2,378.

## Remaining work

1. ~~Patch the per-lane fall-throughs so an unregistered `@extern` aborts with
   the symbol name instead of yielding nil/0/SIGILL.~~ Done for the JIT path
   as warn-only + opt-in strict (above). Still to do: decide whether the
   `@extern`-attribute form reaches the same handler, and measure the SIGILL
   variant reported earlier in this file at the current tip.
2. Narrow the gate's scope to exclude sffi_gen generator inputs, resolve the
   `ffi_`/`sffi_` naming question, then flip it to `--strict` in the pre-push
   guards.
3. Close the `rt_`-prefix hole in the native stub guards (`stubs.rs:477`,
   `llvm_native_link.spl:1825`) — a non-`rt_` symbol is silently given a weak
   `return 0` body today.

## Working the 919 high-confidence core (2026-08-02 lane)

Base: origin `main` @ `e4b4561c803f07e3f7cc7a5882876bd78ab6e3c2`, clean tree
extracted from that sha, `simple-runtime` and the `simple` binary rebuilt from
it. Handoff list: the 919-symbol intersection in `agreed_unbacked.txt`.

### The 919 list re-verified — it holds (PROVED)

Rebuilt the defined-symbol universe independently from the origin-tip source
(Rust `extern "C"` definitions, the C runtime, and every quoted name in
`interpreter_extern/`) = 5,128 distinct names, and separately from the
*freshly built* `libsimple_runtime.a` (`nm --defined-only`) = 17,602 names.

| check | result |
|---|---|
| of the 919, defined anywhere in the source universe | **0** |
| of the 919, defined in the fresh archive | **0** |
| true-positive control (`rt_dict_contains`, `rt_contains`, `rt_value_eq`, `rt_array_len`, `rt_index_of`, `rt_string_lines`) | all found |

The archive is a *supporting* signal only, not the oracle: several real symbols
(`rt_jit_create`, `rt_current_time_ms`, `rt_time_now_seconds`) are absent from
`libsimple_runtime.a` because they live in other crates or behind cargo
features. Absence was therefore always confirmed against source as well.

### The operand-discard hazard does NOT intersect this list (PROVED)

The prohibition "do not implement a receiver for an emitter that discards its
operands" was checked against the list rather than assumed. All eight known
hazard symbols are referenced from the Rust codegen but are **not** members of
the 919:

`rt_enum_unit`, `rt_enum_with`, `rt_pattern_test`, `rt_pattern_bind`,
`rt_par_map`, `rt_par_reduce`, `rt_future_create`, `rt_dict_contains_key` —
each `in_919 = 0`, `in_codegen_tokens = 1`.

More generally: **0 of the 919 are referenced anywhere under
`compiler/src/codegen/`.** The 919 are declaration-side Simple externs, a
disjoint population from the codegen-emitted runtime calls tracked earlier in
this file. Those codegen symbols stay loud and untouched.

### Shape of the 919

| bucket | count |
|---|---|
| referenced from a `.spl` non-declaration line (live call site) | 690 |
| declaration-only, inert | 229 |
| referenced from Rust at all | 14 |
| referenced from `codegen/` | 0 |
| dead (referenced nowhere) | **0** |

The "31 referenced nowhere" figure from an intermediate scan was an artifact of
indexing only `src/`; all 31 (`ptr_const_*`, `ptr_mut_*`, `rt_net_connect`, …)
are referenced from `test/`. Nothing in the 919 is dead, so nothing was deleted
on deadness grounds.

Live-caller families are dominated by subsystems that are simply not built:
`rt_lyon` 49, `rt_arm64` 39, `rt_torch` 38, `rt_arm32` 31, `rt_vk` 25,
`rt_tls13` 24, `rt_cuda` 22, `rt_rv32` 19, `rt_x86` 18. All `@extern`
attribute targets in the tree are `runtime`/`bare`/`browser`/`simple_layout_mark`
— there is no per-external-library targeting, so these are runtime obligations
that the runtime does not meet, not third-party library bindings.

### Near-miss (class b) analysis

28 of the 919 are within 0.90 similarity of a real defined symbol. Most are
*semantic* false matches and were rejected rather than "fixed":
`rt_torch_torchtensor_sin`→`_sum`, `_cos`→`_sub`, `_eye`→`_free`,
`_reshape_Nd`→`_shape`, `rt_ssh_aes128_gcm_*`→`rt_ssh_aes256_gcm_*` (different
cipher), `rt_gc_is_enabled`→`rt_log_is_enabled`, `rt_file_write_bytes_b64`→
`rt_file_write_bytes` (different encoding). Renaming any of these would trade a
loud failure for a silent wrong answer.

Three were confirmed genuine wrong references and fixed.

### Fixed in this change

**1. `rt_cuda_is_available` → `rt_cuda_available`** (real symbol, arity 0, `i64`).
Declared at three sites; the only caller is `cuda_available()` in
`src/lib/nogc_sync_mut/io/cuda_sffi.spl:40`. The corrected call uses the idiom
already established in three other files (`rt_cuda_available() != 0`:
`gc_async_mut/cuda.spl:26`, `gc_async_mut/cuda/mod.spl:14`,
`nogc_async_mut/cuda/mod.spl:664`). The two caller-less declarations
(`nogc_async_mut/engine/physics/backend_gpu/gpu_solver.spl:22`,
`os/ml/gpu_tensor.spl:18`) were deleted rather than renamed — they named a
symbol that does not exist and nothing referenced them.

**2. `rt_time_now_secs` → `rt_time_now_seconds`** in
`src/compiler_rust/lib/std/src/sys/sffi/time.spl:7`. Registered as
`insert_simple!("rt_time_now_seconds", …)`. No callers, so this is a
correctness fix to a declaration table with no behavioural risk.

**3. `get_current_time_ms` → `rt_current_time_ms`** in
`src/compiler_rust/lib/std/src/spec/mode_runner.spl`. This one had **live
callers**: lines 149 and 166 time every multi-mode spec run
(`duration = get_current_time_ms() - start_time`), so the measured duration of
every mode run was derived from an unbacked call. The real symbol is
`native_all/src/lib.rs:1181 extern "C" fn rt_current_time_ms() -> i64`, also
registered for the interpreter. The declaration said `-> i32`; epoch
milliseconds do not fit in `i32`, so the declaration and the three `duration_ms`
type sites (`mode_runner.spl:19`, `mode_reporter.spl:100,103`) were widened to
`i64` in the same change.

### Runtime evidence — RED then GREEN, measured not inferred (PROVED)

Binary: `simple` rebuilt from the base sha (`enum-probe` = 0, i.e. the Rust
seed, which is what `run` uses here).

| mode | probe | rc | output |
|---|---|---|---|
| default (JIT) | unbacked `rt_cuda_is_available` | **0** | ERROR logged, then `-> false` |
| default (JIT) | real `rt_cuda_available` | 0 | `raw -> 0` |
| interpreter | unbacked `rt_cuda_is_available` | **1** | `error: semantic: unknown extern function` |
| interpreter | real `rt_cuda_available` | 0 | `raw -> 1` |

Two corrections to earlier assumptions, both caught by measuring instead of
reasoning:

- The substituted nil in a `-> bool` slot prints **`false`**, not a truthy 3.
  So the pre-fix `cuda_available()` silently answered "no CUDA", it did not
  falsely claim CUDA. The defect is real but its polarity was the opposite of
  what was assumed.
- Exit codes must be read without a pipe. An earlier reading of `rc=0` for the
  interpreter RED case was `tail`'s status, not the compiler's; measured
  directly it is **rc=1**, which matches the handoff.

### Recorded, NOT silently resolved: `rt_cuda_available` diverges by runtime

Hand-computed expectation: this host has two NVIDIA GPUs (`nvidia-smi -L`:
RTX A6000, TITAN RTX), so the correct answer is **1**.

- Interpreter → **1** (correct). Under `#[cfg(not(feature = "cuda"))]` the
  registry shim `interpreter_extern/gpu.rs:1011 rt_cuda_available_fn`
  *dynamically loads* libcuda via `get_cuda_dl()` and counts real devices.
- JIT / native `extern "C"` symbol → **0** (wrong). `cuda_runtime.rs:1358`
  compiles `get_device_count()` to a constant `Ok(0)` when the `cuda` feature is
  off, so `rt_cuda_available()` is blind to the hardware. A third definition,
  `src/runtime/runtime_native.c:183 int64_t rt_cuda_available(void) { return 0; }`,
  hardcodes 0 as well.

Two runtimes, two different detection policies, one compile-time constant
answer. This is not an unbacked-extern defect and it is **not** fixed here — per
policy the divergence is recorded rather than resolved by picking a side. Note
the fix above still strictly improves the caller: previously `cuda_available()`
logged an extern error and returned `false` on both engines; now it returns the
correct `true` on the interpreter and a conservative `false` on JIT/native.

### Left deliberately loud

- **`runtime_set_jit_enabled` / `runtime_set_backend`** — both are in the 919
  and both have live callers in `mode_runner.spl:94,97`. Together with defect 3
  above, *all three* SFFI hooks of the multi-mode spec runner were unbacked,
  which means `run_in_modes(...)` never actually switched execution mode: it
  reports per-mode results while running every "mode" identically. This is a
  false-green generator of the same family as the shim-vacuity findings. It is
  **not** fixed here because backing it requires real runtime mode-switching
  support — a feature, not a rename. Inventing a receiver would convert a loud
  failure into a silent wrong answer.

  **CLOSED 2026-08-02 — as a refusal, and the blast radius is ZERO.** The
  above call was right to leave it loud, and the follow-up found the situation
  is worse *and* harmless in a way the static read could not show:

  1. **`std.spec.mode_runner` did not LOAD AT ALL.** Its module-level
     initializer is `var _current_modes: ModeSet = ModeSet.all()`, but
     `execution_mode.spl` declared `all`/`new`/`interpreter_only`/
     `compiled_only` **without `static`**, so every call on the TYPE failed.
     Importing the module aborted *before `main` started* with `unknown static
     method all on class ModeSet`. Importing via `std.spec` instead left the
     symbol simply absent: `function run_in_modes not found` — while `ModeSet`
     from the sibling module resolved fine, which is the **control that
     verifies the probe fires** and isolates the missing symbol. PROVED.
  2. **`run_in_modes` never reached the externs anyway.** Its body assigned
     `_current_modes` and called `block()` exactly ONCE; it never invoked
     `ModeRunner.set_execution_mode`. So even fully backed externs would not
     have switched anything. PROVED by reading + the load failure above.
  3. **Measured extern behaviour** (probe fires on both sides): under the
     default JIT the call logs `rt_interp_call: function not found:
     runtime_set_jit_enabled`, returns nil, and the program **continues and
     exits 0**. Under `SIMPLE_EXECUTION_MODE=interpreter` it refuses with
     rc=1. Confirms the JIT-only silent path.
  4. **Blast radius: ZERO.** `run_in_modes`, `ModeRunner`, `get_current_modes`
     and `execute_in_mode` have **no callers anywhere in the repo** — no spec,
     test or app. Verified in a clean origin-tip worktree; the shared working
     copy's stale sibling worktrees inflate a naive grep and were the reason
     this looked larger than it is. **No existing result rests on
     `run_in_modes`, so nothing needs re-measuring.** The multi-mode harness
     was never wired up rather than silently lying.

  Fixed by making it **refuse**: the `static` declarations are corrected so the
  module loads, the two unbacked externs are deleted, and both `run_in_modes`
  and `set_execution_mode` now `panic` with an actionable message. In-process
  engine switching is structurally impossible — the engine is chosen once per
  process and `simple test` forces `interpret` for the whole run via
  `run_file_with_interpreter_mode`, ignoring `SIMPLE_EXECUTION_MODE`.
  Multi-mode coverage requires **one process per mode**.

  Also in the same change: this file's `get_current_time_ms` was registered
  nowhere either, so every `duration_ms` in every `TestResult` was fabricated
  on the JIT lane. Routed to `rt_current_time_ms`, which *is* registered.
- The remaining ~685 live-caller symbols belong to unbuilt subsystems (torch,
  lyon, vulkan/wgpu/metal/oneapi, the arm64/arm32/rv32/x86 emulation cores,
  tls13/ssh/quic, gui/gamepad/serial). Registering them per-symbol would be
  unverifiable churn against a detector that reports 0 runtime hits, and several
  would require fabricating semantics. They stay loud.

### Could not exercise, and why

Only the CUDA and time families were exercised end-to-end, because they are the
only ones among the fixed set reachable from a plain `simple run` on this host.
Not exercised: every GPU/graphics family (needs a Vulkan/Metal/oneAPI context),
the emulation cores (`rt_arm64`/`rt_arm32`/`rt_rv32`/`rt_x86`, need a loaded
guest image), `rt_torch` (needs libtorch), and the network stacks
(`rt_tls13`/`rt_ssh`/`rt_quic`, need a live peer). For those the disposition
rests on source evidence only and is labelled INFERRED, not PROVED.

---

# 2026-08-18 — census, the inert-strict-mode defect, and the promotion sequence

## Difficulty: HARD (the default flip), MODERATE (what was actually shipped)

Not because any one change is intricate, but because the blocking constraint is
structural: `interp_call_handler` is `extern "C" -> RuntimeValue` with **no
error channel**. Every failure inside it is already a `RuntimeValue::NIL` by the
time the caller sees it, so "return an error" is not available without changing
the ABI of a symbol the JIT emits calls to. The only two levers inside the
current signature are (a) print a diagnostic and (b) terminate the process.
That is why the strict lane is `process::exit(1)` and not a propagated error,
and why "make it strict" is a policy question about 1,203 real call sites rather
than a code question.

## Defect found and FIXED: `SIMPLE_STRICT_EXTERN=1` was INERT for ~81% of externs

This is the headline. The flag that exists to measure the blast radius could
not see most of the tree.

There are **two** terminal "nothing backs this name" shapes in
`interp_call_handler`, and only one of them armed the diagnostic:

| shape | name form | terminal branch | set `UNBACKED_EXTERN`? |
|---|---|---|---|
| A | un-prefixed | the handler's own `else` arm | yes |
| B | `rt_*` / `spl_*` | `call_extern_function_with_values()` fall-through, `error_utils::unknown_function` → E1002 `unknown extern function: <name>` | **no** |

Shape B is the majority form: **3,206 of 3,952** distinct declared extern
symbols are `rt_`/`spl_`-prefixed. Measured on the deployed seed
(`bin/release/x86_64-unknown-linux-gnu/simple`, md5
`f4d7a685e131bc863042322ce25c8f88`) with two fixtures identical except for the
symbol name:

```
extern fn rt_lane_absent_probe_xyz(x: i64) -> i64
$ SIMPLE_STRICT_EXTERN=1 bin/simple run probe_rt.spl
got 0                                     # rc=0 — no warning, no refusal

extern fn lane_absent_probe_xyz(x: i64) -> i64
$ SIMPLE_STRICT_EXTERN=1 bin/simple run probe_plain.spl
error: extern `lane_absent_probe_xyz` ... refuses to substitute nil for it.
                                          # rc=1 — the sibling DID refuse
```

So the earlier "SIMPLE_STRICT_EXTERN=1 exists and works" was true only for the
746 un-prefixed symbols. A flag that looks like a safety net and catches nothing
is worse than no flag: it converts an open question into a false all-clear.

**Fix** (`src/compiler_rust/compiler/src/interpreter_sffi.rs`, the `Err` arm of
`interp_call_handler`): shape B is now recognised by its exact E1002 message,
anchored to `name`, and arms the same diagnostic. Anchoring to the name matters
— E1002 is also raised for ordinary undefined calls, so the code alone would
misattribute an error raised *inside* a real extern body.

**This is warn-only by default, so it changes no program's value and no exit
status.** Verified: the default lane still prints `got 0` and exits 0 for both
shapes; only a once-per-name stderr warning is new (silenceable with
`SIMPLE_QUIET_EXTERN_WARN=1`).

Regression guard: `scripts/check/check-unbacked-extern-diagnostic.shs`
(3 fixtures × 2 lanes = 6 probe runs; asserts warn-only keeps rc 0, strict
gives rc 1 and specifically **not** 134). Proven RED-before / GREEN-after:

```
$ SIMPLE_BIN=<pre-fix seed>  sh scripts/check/check-unbacked-extern-diagnostic.shs
FAIL — 6 probe run(s) checked, defects found:
  - [rt_prefixed]  default lane printed no unbacked-extern warning ... INERT
  - [rt_prefixed]  strict lane exited 0, expected 1 ... INERT
  - [spl_prefixed] (same two)  ... rc=1
$ SIMPLE_BIN=<rebuilt seed>  sh scripts/check/check-unbacked-extern-diagnostic.shs
PASS — 6 probe run(s) checked, unbacked-extern diagnostic armed on all shapes
```

The un-prefixed probe passes on **both** binaries, which is what isolates the
failure to shape B rather than to the harness.

## The census

Reproduce: `sh scripts/check/extern-backing-census.shs <out.tsv>`.
Data: `doc/08_tracking/bug/data/unbacked_extern_census_2026-08-18.tsv`.

**3,952 distinct extern symbols** across 14,898 declaration sites (owned scope,
`src` + `test`, vendored excluded).

| n | class | backed? |
|---|---|---|
| 1,418 | `in_deployed_binary` — defined symbol per `nm --defined-only` | yes |
| 663 | `interp_extern_registry` — name-dispatched in `interpreter_extern/**` | yes |
| 59 | `libc_libm` — resolvable by dlsym | yes |
| 38 | `bare_exempt` — `@extern("bare", …)`, freestanding by design | exempt |
| 165 | `c_runtime_source_only` — in owned `src/runtime/*.c`, absent from the seed | native lane only |
| 49 | `rust_source_feature_gated` — `pub extern "C" fn` present, absent from this build | build-config |
| 10 | `external_library_symbol` — SDL/gl/cu/vk… from a dlopen'd lib | if installed |
| 85 | `SHADOWED_BY_SPL_FN` — a pure-Simple `fn` of that name exists | ambiguous |
| **262** | **`DEAD_DECLARATION`** — zero call sites in the declaring module | ~~deletable now~~ **NOT deletable — see Stage 2, verified 2026-08-18: 0 of 262 are unreferenced** |
| **1,203** | **`GENUINELY_MISSING`** — live module-scoped call sites, no backing found | **no** |

Two methodology points, both of which move the number materially:

- **The old ~919 figure came from a text scan.** `check-extern-registration.shs`
  scores a symbol "registered" when `sym(` appears anywhere in any `.c/.h/.rs`
  file — every **call site** counts as evidence of a **definition**. This census
  uses real symbol tables (`nm`) plus the interpreter's name-dispatch literals.
- **Call sites are counted MODULE-SCOPED**, not tree-wide. Simple resolution is
  module-scoped, so a tree-wide count credits name collisions
  (`env_get` 2,442 "calls", `json_parse` 283, `path_join` 176, `size_of` 115)
  to an extern those calls never reach. Tree-wide scoring inflated
  GENUINELY_MISSING from 1,203 to 1,320 purely that way.

### Where the 1,203 live

| n | declaring area |
|---|---|
| 212 | `src/os/kernel` |
| 205 | `src/lib/nogc_sync_mut` |
| 171 | `src/app/io` |
| 151 | `src/compiler_rust/lib` |
| 66 | `src/lib/common` |
| 49 | `src/lib/gc_async_mut` |
| 41 | `src/os/drivers` |

Largest single families by module-scoped call volume: `spl_free_buffer` (351),
`spl_load_i64` (195), `rt_push_byte` (194), `spl_alloc_buffer` (186),
`spl_store_u8` (170) — i.e. the T32/SFFI buffer family and
`src/runtime/simple_core/core_array.spl`'s raw memory primitives.

## Why the default was NOT flipped — with the evidence

**No subset boundary in this tree is clean.** That is the finding that kills the
obvious stage-2 design. Every top-level area has GENUINELY_MISSING symbols:

```
374/1469  src/lib          370/ 575  src/os        207/ 668  src/app
151/ 805  src/compiler_rust  61/ 236  src/compiler   27/  67  test/01_unit
```

So "strict for a named clean prefix or directory" cannot be implemented today —
there is no such prefix and no such directory. Flipping globally would turn
1,203 symbols with live call sites into hard process exits. **Not done, and it
should not be done as a flag flip.**

## Sequenced promotion

- **Stage 0 — clean refusal** (DONE, `8beeb621c70f`). Strict mode exits 1 with a
  diagnostic instead of `abort()`/134/core dump.
- **Stage 1 — arm the diagnostic on ALL shapes** (DONE, this change). Warn-only
  default, so nothing breaks; `SIMPLE_STRICT_EXTERN=1` becomes meaningful for
  the 3,206 `rt_`/`spl_` symbols it previously ignored. **Breaks nothing:
  measured — same values, same exit statuses, one new stderr line per distinct
  name.** Without this stage every later stage is unmeasurable, which is the
  real reason it comes first.
- **Stage 2 — delete the 262 `DEAD_DECLARATION` symbols. ABANDONED 2026-08-18
  after verification: 0 deleted, and the class is not deletable as computed.**
  The original claim below is left in place because it is what was disproved.
  *(Original: "Zero call sites in their declaring module, so removal is a no-op
  at runtime and shrinks the surface by 15% of the candidate set for free.
  Breaks nothing by construction; each deletion is individually verifiable by
  re-running the census.")*

  Independent tree-wide re-verification of all 262
  (`doc/08_tracking/bug/data/dead_declaration_verification_2026-08-18.tsv`,
  produced by a `sym(`-literal scan plus a bare-word scan over
  `src test scripts doc`, excluding each symbol's own declaring files):

  | finding | count |
  |---|---|
  | claimed `DEAD_DECLARATION` | 262 |
  | **have a real `.spl` call site in another file** | **70** |
  | have a non-`.spl` code/script/test reference (`.rs`/`.c`/`scripts/`) | 41 |
  | referenced only from `doc/` (documented public API surface) | 111 |
  | **have NO reference of any kind outside the declaring file** | **0** |
  | **deleted** | **0** |

  Two independent defects in the classification, both of which make
  `DEAD_DECLARATION` mean something other than "dead":

  1. **Module-scoped call counting is fail-open for libraries.** The census
     counts callers only in the declaring file's own directory. Every one of
     these declarations lives in a binding module whose entire purpose is to be
     called from *elsewhere* — 173 of the 262 are declared under `src/lib/**` or
     `src/compiler_rust/lib/std/**` (public stdlib), 29 under
     `sffi_gen/specs/**` and `ffi_gen.specs/**` (input specifications to a code
     generator, where zero callers is the correct steady state), 39 under
     `src/os/**`. "Zero callers in my own directory" is the *normal* state for a
     public API, not evidence of death. 70 symbols have a hard `.spl` call site
     one directory away and were still scored dead.
  2. **The `external_library_symbol` prefix list is incomplete, so its misses
     fall through into `DEAD_DECLARATION`.** `DEAD_DECLARATION` is a residual
     class reached only after every backing tier fails, so any gap in an earlier
     tier lands here. `lua_*`/`luaL_*` (`src/lib/nogc_sync_mut/lua/lua_sffi.spl`)
     are Lua C API symbols resolved from a `dlopen`'d liblua and are absent from
     the `EXT` prefix tuple. The GPU/SIMD kernel intrinsics
     (`local_id`, `group_id`, `local_size`, `num_groups`, `mem_fence`,
     `barrier_and_fence`, `src/compiler_rust/lib/std/src/gpu/kernel/**`,
     `ext/simd/sffi.spl`) are never host symbols at all — they are lowered by
     the GPU/SIMD backend at codegen time, so "not in `nm` output" is expected
     and carries no information about liveness.

  The residual 192 with no `.spl` caller are all either documented public API,
  generator spec input, arch intrinsics, or `rt_*` runtime hooks that represent
  unimplemented intent (`rt_ed25519_generate_keypair` in
  `src/app/package.registry/signing.spl`; `rt_test262_eval` /
  `rt_test262_load_corpus` in `src/app/ui.chromium/js_audit.spl`). Per the repo
  rule on unimplemented intent, none of those may be deleted as dead weight.

  **Consequence for Stage 3.** The frozen baseline must be built over the
  *union* of `GENUINELY_MISSING` and `DEAD_DECLARATION` (1,465), not over the
  1,203 alone — treating the 262 as removed would ratchet 262 live, mostly
  public-API declarations straight to fatal. Before any future deletion pass,
  the census needs: cross-module call counting (import-aware, not
  directory-scoped), a `lua_`/`luaL_` entry in the `EXT` prefix tuple, and a
  backend-intrinsic tier for the GPU/SIMD kernel namespace.
- **Stage 3 — baseline ratchet, NOT a prefix.** Since no directory is clean, the
  boundary must be the census itself: strict-by-default for any unbacked extern
  **not** in a frozen baseline (the 1,203, checked in as the census TSV), while
  baselined symbols stay warn-only. Effect: every **new** unbacked extern is
  fatal from day one; the existing backlog cannot grow. This is the same
  ratchet pattern as `test_tree_divergence_baseline.txt` and
  `extern_abi_signature_baseline.txt`. Cost to be measured before landing: one
  baseline load per process in a hot path; the diagnostic is already
  once-per-name so the lookup can be too.
- **Stage 4 — retire families, shrink the baseline.** Ordered by call volume:
  the `spl_*` buffer/memory family (~1,100 module-scoped calls across ~10
  symbols) first, then `src/os/kernel` (212 symbols — many of which are
  arguably mis-tagged and should carry `@extern("bare", …)`, which would move
  them to `bare_exempt` rather than requiring an implementation).
- **Stage 5 — global strict default**, only once the baseline reaches zero.
  Not before, and not on a schedule.

Note that stage 4's kernel bucket is partly a **tagging** problem, not an
implementation problem: 370 of 575 `src/os` externs are unbacked on the host
because they are freestanding, yet only 38 symbols tree-wide carry the `bare`
ABI tag. Correctly tagging those is cheaper than implementing them and is
probably the single highest-leverage item in the backlog.

## Not fixed here

The native/AOT lane's weak-stub fabrication is a **separate** defect with its
own record
(`native_build_fabricates_weak_stub_for_unimplemented_extern_2026-08-18.md`).
This change is JIT/interpreter-lane only. Confirmed still reproducing: the
un-prefixed probe returns `got 3` — a fabricated value, not nil — under the
default lane on both the old and the new binary.
