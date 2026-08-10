# `rt_*` extern ABI divergence across the three runtime implementations

**Date:** 2026-08-10
**Status:** 1 FIXED (`rt_file_is_char_device`), 19 RED (filed here)
**Parent:** `doc/08_tracking/bug/rt_file_is_char_device_dejit_and_dual_abi_2026-08-10.md`

## What was fixed

`rt_file_is_char_device` had **four** definitions, not three:

| definition | old ABI |
|---|---|
| `src/runtime/runtime.c:963` | `int (const char*)` — 1 arg |
| `src/runtime/runtime_native.c:7618` | `int (const char*)` — 1 arg |
| `src/runtime/runtime_native_gpu_stub.c:41` | `int (const char*)` — 1 arg — **this is the copy linked into the Rust seed** |
| `src/compiler_rust/runtime/src/value/sffi/file_io/metadata.rs:40` | `(ptr, len) -> bool` — 2 args |

### Reproduction (before the fix)

```
$ src/compiler_rust/target/release/simple run q12_repro.spl      # JIT
zero=false   null=false   tty=true   readme_is_file=true  src_is_dir=true
$ SIMPLE_EXECUTION_MODE=interpreter ... run q12_repro.spl        # interpreter
zero=true    null=true    tty=true   readme_is_file=true  src_is_dir=true
```

`/dev/zero` and `/dev/null` are character devices. `tty=true` in both lanes is the
tell: the C copy received a **non-NUL-terminated** pointer and read whatever bytes
followed in the constant pool — `/dev/tty` happened to be followed by a `\0`, the
other two were not. `is_file` / `dir_exists` were fine, so extern-bool is not
broadly broken; the defect was symbol-specific.

### ABI chosen: `(ptr, len)`

The compiler is the authority and it already emits two arguments:

- `src/compiler_rust/compiler/src/codegen/runtime_sffi.rs:1838` — `&[I64, I64] -> &[I8]`
- `src/compiler/50.mir/text_extern_abi.spl:69` — decomposes `text` into `(ptr, len)`

A Simple `text` is **not NUL-terminated**, so a `const char*` ABI is unsound here
by construction, independently of which definition wins the link. The C
definitions were the ones out of step.

### Fix location

The defect straddles the C runtime and the ABI contract; it was fixed **in the C
runtime**, leaving both the Simple and Rust layers untouched:

- `src/runtime/runtime_native_gpu_stub.c` — duplicate **deleted**. The Rust
  runtime gained its own canonical definition on 2026-08-10 (`b68d7a2d461`), so
  this seed-only copy is now redundant as well as wrong; its header comment
  records why it must not come back.
- `src/runtime/runtime.c`, `src/runtime/runtime_native.c`, `src/runtime/runtime.h`
  — converted to `int rt_file_is_char_device(const uint8_t*, uint64_t)`, copying
  into a bounded buffer before `stat(2)`. These serve the AOT/native lanes, which
  use the same `text_extern_abi.spl` decomposition and were therefore equally
  wrong.

There were **zero** C-internal callers of this symbol, so the change is closed.

## Family enumeration

Method: parse every `rt_*` **definition** (not declaration) out of
`src/runtime/runtime.c`, `runtime_native.c`, `runtime_native_gpu_stub.c` and every
`extern "C" fn rt_*` under `src/compiler_rust/runtime/src/value/sffi/**`, and
compare arity against `RuntimeFuncSpec` in
`src/compiler_rust/compiler/src/codegen/runtime_sffi.rs`. Scanner:
scratch script, 1,064 symbols / 1,122 compiler declarations.

**Positive control.** The pre-fix run of the same scanner reported the known
defect, which is why the scan is trusted:

```
 rt_file_is_char_device   decl=2  {'runtime.c': 1, 'runtime_native.c': 1, 'metadata.rs': 2}
```

Post-fix it is absent from the output. All remaining rows are new findings.

| symbol | compiler decl | runtime.c | runtime_native.c | gpu_stub.c | Rust SFFI |
|---|---|---|---|---|---|
| `rt_dir_create` | 3 | — | 2 | — | directory.rs=3 |
| `rt_dir_create_all` | 2 | — | 1 | — | directory.rs=2 |
| `rt_dir_exists` | 2 | 1 | 1 | — | metadata.rs=2 |
| `rt_dir_glob` | 2 | — | — | — | directory.rs=4 |
| `rt_dir_walk` | 2 | 1 | — | — | directory.rs=2 |
| `rt_file_copy` | 4 | 2 | — | — | file_ops.rs=4 |
| `rt_file_exists` | 2 | 1 | 1 | — | metadata.rs=2 |
| `rt_file_find` | 4 | — | — | — | directory.rs=5 |
| `rt_file_fsync` | 2 | 1 | — | — | file_ops.rs=2 |
| `rt_file_fsync_cached` | 2 | 1 | — | — | file_ops.rs=2 |
| `rt_file_is_regular_no_follow` | 2 | 1 | 1 | — | metadata.rs=2 |
| `rt_file_move` | 4 | — | 2 | — | file_ops.rs=4 |
| `rt_file_open` | 4 | — | 2 | — | descriptor.rs=6 |
| `rt_file_read_text` | 2 | 1 | 1 | — | file_ops.rs=2 |
| `rt_file_size` | 2 | 1 | 1 | — | file_ops.rs=2 |
| `rt_file_stat` | 2 | 1 | — | — | metadata.rs=2 |
| `rt_mkdir_p` | — | — | 1 | — | directory.rs=2 |
| `rt_panic` | 2 | — | 1 | — | contracts.rs=2 |
| `rt_process_run_with_limits` | 5 | — | — | — | env_process.rs=8 |

TOTAL MISMATCHES: 19 (of 1064 rt_* symbols scanned, 1122 compiler decls)

Numbers are argument counts. `—` = no definition in that lane.

### Two distinct failure classes

**Class 1 — C lane still uses the C-string ABI (14 symbols).** Every row where a
C file says 1 and the compiler + Rust say 2 (or C says 2 and they say 4) is the
same defect just fixed for `rt_file_is_char_device`: a `text` argument pair
collapsed to a single `const char*`. `rt_dir_exists`, `rt_file_exists`,
`rt_file_is_regular_no_follow`, `rt_file_read_text`, `rt_file_size`,
`rt_file_stat`, `rt_file_fsync`, `rt_file_fsync_cached`, `rt_dir_walk`,
`rt_file_copy`, `rt_file_move`, `rt_dir_create`, `rt_dir_create_all`,
`rt_mkdir_p`, `rt_panic`. These are only latent while the Rust definition wins
the link in a given lane — in any lane where the C copy wins (as it did for
`rt_file_is_char_device` in the seed) they silently return wrong answers or read
out of bounds. Not fixed here because several have C-internal callers
(`rt_dir_create` 4, `rt_dir_walk` 3, `rt_file_fsync` 2, `rt_dir_exists` 1,
`rt_dir_create_all` 1) and each needs its own call-site audit and reproduction.

**Class 2 — the compiler declares a different arity than the ONLY implementation
(4 symbols).** These are worse: there is no ABI to pick between, the compiler is
simply calling with the wrong number of arguments, so the callee reads
uninitialised registers.

| symbol | compiler passes | implementation expects |
|---|---|---|
| `rt_dir_glob` | 2 (`pattern`) | 4 (`dir_ptr, dir_len, pattern_ptr, pattern_len`) |
| `rt_file_find` | 4 | 5 (trailing `recursive: bool`) |
| `rt_file_open` | 4 | 6 |
| `rt_process_run_with_limits` | 5 | 8 |

`rt_dir_glob` is verified by inspection: `runtime_sffi.rs:1885` declares
`&[I64, I64]` with the comment `// pattern -> RuntimeValue (array)`, while
`directory.rs:199-207` takes four parameters and forwards to `rt_file_find`. The
`dir` argument the implementation reads is whatever the caller left in the first
two registers.

## `-z muldefs` recommendation: keep it, but add a gate — do not remove

Removing it is **not** feasible as a drop-in. `scripts/check/check-runtime-bundle-duplicate-symbols.shs:30`
records that `ld.lld-18` without muldefs reports **20** duplicate-symbol errors on
the runtime bundle, and the C-lane duplicates are largely deliberate (the same
body must be reachable from the core-c-bootstrap capsule, the native product
build, and the seed, which link disjoint object sets). Dropping the flag would
break the AOT/native link outright until all 20 are re-layered into per-lane
archives — that is the real cost, and it is a multi-day refactor of
`build-core-c-bootstrap-runtime-capsule.shs` plus the runtime source layout.

What is cheap and closes the actual hole: the flag is not what made this silent —
**the absence of an ABI gate** is. `scripts/check/check-runtime-bundle-duplicate-symbols.shs`
already enumerates duplicate definitions against a baseline; it compares
*presence*, not *signature*. Extend it (or add a sibling) with the scan in this
document: for every symbol with more than one definition, assert the arities
agree with `runtime_sffi.rs`. That converts all 19 rows above from invisible into
a failing check, without touching the linker flags.

Note also that the seed's own `libsimple_runtime.so` link does **not** use
muldefs — it hard-errored `duplicate symbol: rt_file_is_char_device` the moment
the Rust definition landed. The stale prebuilt `libruntime_sffi_c.a` in
`target/release` was masking that; a clean build would have caught this one.
