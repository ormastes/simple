# JIT de-JITs whole stage1: `rt_native_build` + `runtime_file_rename` unresolved (2026-08-22)

**Status:** FIXED
**Class:** unresolved `Linkage::Import` de-JITs the whole module — the same
class as `jit_unresolved_rt_process_read_stdout_checked_2026-08-22.md` and
`jit_runtime_symbol_unregistered_rt_value_unbox_int_2026-08-11.md`. Two symbols,
**two different root causes**, recorded together only because they were the two
remaining blockers on the same stage1 compile.

## Symptom

```
[jit-fallback] unresolved external symbol 'rt_native_build': whole module dropped to the interpreter
[jit-fallback] unresolved external symbol 'runtime_file_rename': whole module dropped to the interpreter
```

Reproduced against seed `/mnt/data/seedperf/simple.f593e9ce8dd` with
`native-build src/app/cli/bootstrap_main.spl`. One unresolvable name fails the
whole `compile_module` (`codegen/jit.rs::first_unresolved_import`), so every
function in stage1 interprets (~100-1000x).

## Symbol 1 — `rt_native_build`: a real definition in a crate nothing can link

Not a missing implementation. `native_all/src/lib.rs:143` defines it, correctly
and completely. The problem is *where*: `native_all` is
`crate-type = ["staticlib"]`, so **no crate can depend on it** — including the
seed binary. Measured: `nm <seed> | grep -c ' T rt_native_build'` = **0**.

The layering intent was real and is preserved: `pipeline/native_project/config.rs:77-90`
already documents that `rt_native_build` "IS the native-build driver", that
there is no C body and there cannot be one, and that the bootstrap lane must
*select* the hosted archive rather than widen the core C ABI. Nothing about that
requires the definition to sit in the staticlib. Its entire dependency set
(`simple_compiler::pipeline::{NativeBuildConfig, NativeProjectBuilder}`,
`simple_compiler::optimizations`, `simple_runtime::value`) is in or below
`simple-compiler`.

Also note the interpreter could not stand in: `interpreter_extern/mod.rs:1607`
registers it to `cli::rt_native_build`, which is `interpreter_not_supported`.

### Fix (a: link/register the existing definition; NOT a stub)

1. **Relocated** the one definition and its helpers to
   `compiler/src/native_build_sffi.rs`. No second definition; no behaviour change.
2. `native_all` now does `pub use simple_compiler::native_build_sffi::rt_native_build;`.
   It already carries `pub use simple_compiler;`, which is exactly how the
   `rt_cranelift_*` symbols defined in `simple-compiler` are rolled into
   `libsimple_native_all.a` today — so **the staticlib's exported symbol set is
   unchanged**.
3. `RUNTIME_SYMBOL_NAMES` is generated from the runtime crate + C runtime and
   cannot list a compiler-owned symbol, and a Rust `bin` does not put its
   `#[no_mangle]` symbols in the dynamic symbol table, so `dlsym` misses too.
   Added `codegen::jit::COMPILER_OWNED_RUNTIME_SYMBOLS` /
   `compiler_owned_symbol()` — a table of **real function addresses**, published
   to `JITBuilder` and consulted by `jit_import_resolves` so the guard's answer
   and the JIT's actual resolution stay identical. A stub returning nil was
   deliberately NOT written: that is the
   `unregistered_extern_silent_nil_2026-08-01.md` defect class.

Measured after: `nm <seed> | grep -c ' T rt_native_build'` = **1**.

## Symbol 2 — `runtime_file_rename`: not a runtime symbol at all

There is nothing to define, and defining anything would have been wrong.
`runtime_file_rename` is a **local alias** created by
`src/lib/nogc_sync_mut/io/file_ops.spl:218`:

```
use std.io_runtime.{file_rename as runtime_file_rename}
```

`hir/lower/lowerer.rs::collect_flattened_import_aliases` resolves such aliases
from the flattener's import-binding markers, in two tiers: the owner-mangled
symbol, else the bare `source_name` **if it is unique in the flattened unit**.
Neither tier fired here. Only `main` is owner-mangled
(`pipeline/module_loader.rs:668-686`), so tier 1 found nothing; and the
flattened unit contains **four** `file_rename` definitions (`io_runtime.spl:424`,
`file_system/file_ops.spl:145`, `fs.spl:643`, `io/file_ops.spl:220`), so tier 2
refused as ambiguous and left the alias unresolved — becoming a
`Linkage::Import` named after the *alias*.

### Fix (b: resolve it where it belongs — HIR, not the runtime)

Added a third tier keyed on the flattener's own module-owner tag
(`tag_function_module_owner`): if exactly one function named `source_name` is
tagged with the marker's `source_owner`, bind the bare name. This is not a
guess. The **non-aliased** spelling `use std.io_runtime.{file_rename}` is
already used in the tree (`src/lib/nogc_sync_mut/shell/file.spl:22`) and already
lowers to exactly that bare name; refusing only the aliased spelling made the two
forms disagree. The conservative "do not guess" branch is retained for the case
this tier cannot decide either.

## Sweep — 83 more of the same shape

`compiler/tests/native_build_and_alias_symbols_registered.rs` sweeps all
**1831** names in `RUNTIME_SYMBOL_NAMES` against the exact predicate the JIT
uses. **83 unique names have no definition reachable from the seed** — the same
population `check-no-unresolved-runtime-symbols.shs` reports RED. Too large to
fix here, so it is frozen as `UNRESOLVED_BASELINE` in that test: a NEW
unresolvable name fails, and a baselined name that became resolvable fails as a
**stale baseline**. Families: `rt_tls13_hkdf_*` (13), `rt_webgpu_*` (8),
`rt_simpleos_*_bytes` (8), `rt_torch_torchtensor_*_checked` (8),
`__simple_runtime_matrix_f64_*`/`gemm` (6), `rt_cuda_event_*` (5),
`rt_pbkdf2_hmac_*` (4), `rt_call_ptr_[0-3]` (4), `native_{tcp,udp}_set_*_timeout` (4),
`rt_vulkan_timestamp*` (3), `rt_process_owned_*` (3), plus singles including
`rt_dict_insert`, `rt_hostname`, `rt_char_from_code`, `rt_system_cpu_count`,
`rt_process_run_owned_bounded_value`.

## Regression gate

`src/compiler_rust/compiler/tests/native_build_and_alias_symbols_registered.rs`
— 3 tests: `rt_native_build` resolvable; the compiler-owned table is live and
discriminates (non-empty, every listed name has an address, a nonexistent name
is refused); and the ratcheted sweep with its own non-vacuity assertions.
Fails pre-fix on `rt_native_build`, passes post-fix.

---

# REOPENED 2026-08-23 — symbol 2's fix was only half the compiler

**Status:** FIXED (second half)

The `runtime_file_rename` fix above was landed in **HIR lowering**
(`hir/lower/lowerer.rs::collect_flattened_import_aliases`). That is the
**codegen/JIT** path, and it is genuinely correct for that path. But the alias
is resolved *independently* by the **interpreter**, which `c0c4e707789` never
touched — and `simple test` runs specs in interpreter mode
(`Running N test file(s) [mode: interpreter]`). So on the path that matters most
to the project, the symbol stayed unresolved.

## Symptom (three lanes, same day)

```
Results: 1 total, 1 passed, 0 failed
All tests passed!
error[E1002]: function `runtime_file_rename` not found
$ echo $?
1
```

A **fully green** suite exits 1. `print_summary`
(`test_runner_main.spl:1125`) prints the clean `Results:` block first; then
`update_test_database` (`:1144`) dies. Everything after that point — including
the `test_result.md` write at `:1193` — never runs.

## Why the first fix did not cover it

`E1002` here is `codes::UNDEFINED_FUNCTION` emitted at
`compiler/src/interpreter_call/mod.rs`, not by HIR lowering. Flattening *does*
record the alias edge — `record_flattened_import_binding` writes
`local alias -> (defining owner, defining name)` into
`MODULE_GLOBAL_BINDINGS_BY_OWNER` — but that table was only ever consulted for
**globals**. A *call* of `runtime_file_rename` looked the bare alias up in the
interpreter's `functions` map, missed, and fell straight through to E1002.

Hypothesis explicitly tested and **refuted**: "the deployed seed simply predates
`c0c4e707789`". A seed rebuilt from clean HEAD (which contains `c0c4e707789`)
reproduced the failure byte-for-byte. The fix was incomplete, not undeployed.

## Fix (interpreter-side counterpart; not a stub, nothing swallowed)

Immediately before the E1002 emission, resolve the name through
`owner_bindings(CURRENT_EXEC_MODULE)` to `(source_owner, source_name)` and
dispatch to the owner-mangled symbol (`flatten_owner_mangled_name`), or else to
the candidate whose `function_module_owner` **equals `source_owner`**.
Resolution is **delegated to the same recorded binding the HIR side uses**, so
codegen and the interpreter cannot disagree about which of the four
`file_rename` definitions an alias names. When no candidate matches the owner we
fall through to E1002 rather than guess.

### Why selection MUST be by owner, not by bare name (first attempt, measured)

The first version of this fix fell back to `functions[source_name]` when the
mangled symbol was absent, guarded only by `source_name != name`. That guard is
insufficient and the attempt **failed on the runner**:

```
All tests passed!
error: stack overflow: recursion depth 1000 exceeded limit 1000 in function 'file_rename'
```

Flattening mangles only `main`, so all four `file_rename` definitions share the
one bare key. For `runtime_file_rename` the bare key holds `io/file_ops`'s own
one-line wrapper — the very function whose body issued the call — so the alias
resolved back into its own caller and recursed. The name-inequality guard cannot
see this, because the two names genuinely differ; only the OWNER distinguishes
the wrapper from the definition it wraps. This is the same ambiguity the HIR
side had to solve, and it has to be solved the same way.

Deliberately NOT done: stubbing the symbol (that is the
`unregistered_extern_silent_nil_2026-08-01.md` defect class), and making the
runner tolerate a failed DB write (a silent write failure is precisely how the
DB became stale).

## Measured, same all-passing fixture, pre-fix seed vs post-fix seed

| | exit | E1002 | `test_db.sdn` |
|---|---|---|---|
| pre-fix | **1** (on `All tests passed!`) | yes | **not written** |
| post-fix | **0** | none | **rewritten** |

## Consequence — this is what froze the test DB

`doc/08_tracking/test/test_result.md` read `Total 770 / Passed 0 / Failed 0`
with `test_db.sdn` last written **2026-08-22 09:43**. That is a **stale
snapshot, not a corrupted write**: every run after the bad seed aborted before
writing anything, so nothing was half-written and regeneration is safe. This
also explains the incoherent joins reported separately — those rows are simply
old.

## Regression gate

`scripts/check/check-test-db-write-succeeds.shs` over
`test/01_unit/tools/test_db_write/`. It EXECUTES the runner: no existing guard
could catch this, because every one of them checks trees, ranges, or source
text, and the two that run a toolchain run it over SOURCE. A runner that exits
non-zero on a green suite is well-formed by all of those measures. Asserts exit
0 AND that the DB was actually rewritten (mtime forced backwards first, so
"rewritten" is a fact rather than an inference); the runner's exit status is
read directly into a variable, never through a pipe. Fails pre-fix, passes
post-fix.

## Known gap, not fixed here

`test_result.md` still did not update in the post-fix run even though
`test_db.sdn` did. The `:1193` write sits under `match db { Ok(database) => ...`
and is silently skipped on `Err(_)`. That silent skip is a second defect of the
same family and is NOT addressed by this change.

## STATUS CORRECTION — the interpreter half is NOW FIXED (`aac03e9d65a`, 2026-08-23)

The `**Status:** FIXED` at the top of this record was **correct for the JIT /
codegen path and wrong for the interpreter path** until `aac03e9d65a`. Both
halves are now fixed. Kept as history because the window was real. Evidence,
so this is not a matter of opinion: a seed rebuilt from clean `HEAD` — a tree
that demonstrably CONTAINS `c0c4e707789` — reproduces the original symptom
byte-for-byte. The fix is incomplete, not undeployed. Anyone reading only the
header will lose hours re-deriving that.

## Approaches TRIED AND FAILED — do not retry these

All three compiled, all three looked right in review, all three failed when
actually executed against the runner. Recorded because each is the obvious next
idea.

1. **Bare-name fallback**, guarded on `source_name != name`.
   → `stack overflow: recursion depth 1000 exceeded in function 'file_rename'`.
   Flattening mangles only `main`, so all four `file_rename` definitions share
   one bare key, and that key holds `io/file_ops`'s own wrapper — the very
   function issuing the call. The name-inequality guard cannot see this because
   the two names genuinely differ; only the OWNER separates wrapper from wrapped.

2. **Match `function_module_owner(candidate) == source_owner`.**
   → never matched; fell through to the original E1002. `source_owner` names the
   **facade** `src/lib/io_runtime.spl`, not the declaring module
   `src/lib/nogc_sync_mut/io_runtime.spl`.

3. **Facade chain-walk (bounded 16 hops) + last-resort "not owned by the current
   module" filter.**
   → `stack overflow` again. The filter used `is_none_or(...)`, which KEEPS
   candidates whose owner is unknown — and the wrapper is one of them, so it
   survived the filter. Any future filter here must treat "unknown owner" as
   *reject*, not *accept*.

The next attempt should start from the `SIMPLE_DEBUG_ALIAS=1` dump (see below)
rather than from another inference.

## Instrumentation kept on purpose

`SIMPLE_DEBUG_ALIAS=1` dumps, at the resolution point: the calling module, the
binding's `source_owner`/`source_name`, every candidate's
`function_module_owner`, whether the owner-mangled symbol is present, and the
next hop in the binding chain. Default OFF, retained per
`doc/07_guide/infra/logging/log_retention_policy.md` and following the
`SIMPLE_AMBIGDBG` precedent for this same defect class. Alias resolution has now
cost four separate investigations; the next person should not have to rebuild
this from scratch.

## The test DB is STALE, not corrupt — regeneration is SAFE

Recorded explicitly because fear of destroying data has been blocking
regeneration. `doc/08_tracking/test/test_result.md` reading
`Total 770 / Passed 0 / Failed 0`, and `test_db.sdn` with counter rows whose
`tests -> suites -> files` joins disagree, are **an old snapshot from
2026-08-22 09:43 that simply stopped being updated**. They are not a
half-written or torn file. The abort happens INSIDE `update_test_database`
(`test_runner_main.spl:1144`) — measured by forcing both files' mtimes to a
sentinel and observing that a failing run leaves BOTH untouched. Nothing is
partially written, so regenerating the DB destroys no information that is not
already reproducible from a test run. Once the interpreter half lands,
regenerate rather than attempting a repair.

## RETRACTED — the "second defect" was a phantom

An earlier revision of this record filed `test_result.md`'s write
(`test_runner_main.spl:1193`, under `match db { Ok(database) => ...,
Err(_) => () }`) as an independent second defect, on the evidence that it
stayed unwritten on a run where `test_db.sdn` succeeded. That was wrong: on the
FIXED seed both files write. The `Err(_)` arm was being taken because
`update_test_database` had died — it was downstream of the same abort, not a
separate bug. Retracted rather than left standing, because a phantom defect
record costs the next reader real time.

The `Err(_) => ()` arm is still silent, and that remains a legitimate
robustness concern worth a future look — but it is NOT what caused this
incident and should not be filed as though it were.
