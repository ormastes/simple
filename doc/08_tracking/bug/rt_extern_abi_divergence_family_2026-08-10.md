# `rt_*` extern ABI divergence across the three runtime implementations

**Date:** 2026-08-10
**Status:** RESOLVED -- all 19 rows fixed. Class-2 (4) fixed in `52c6089581c`/`3997bffde05`/`1abc0c9d7a7`; Class-1 (15 symbols / 21 baseline rows) fixed 2026-08-10, see "Resolution" at the end. `scripts/check/extern_abi_signature_baseline.txt` is now EMPTY.
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


## Resolution (2026-08-10) -- Class 1 closed, baseline empty

All 15 Class-1 symbols were converted to the `(ptr, len)` ABI in the **C
runtime** (the layer that was out of step; the Simple and Rust layers already
agreed). Each was reproduced first, against the real translation units, by
calling the definition through the ABI the compiler actually emits with a
**non-NUL-terminated** buffer -- the layout of any `text` produced by slicing or
concatenation -- and re-verified afterwards in every C link order, since
`-z muldefs` makes link order decide which definition wins.

Not one proved benign. Representative before/after:

| symbol | before (non-NUL-terminated path) | after |
|---|---|---|
| `rt_file_exists` | 0 | 1 |
| `rt_dir_exists` | 0 | 1 |
| `rt_file_is_regular_no_follow` | 0 | 1 |
| `rt_file_size` | -1 | 3 |
| `rt_file_stat` | 0 | 1755993622 |
| `rt_file_read_text` | `[]` len=0 | file content |
| `rt_file_fsync` / `_cached` | 0 | 1 |
| `rt_file_copy` / `rt_file_move` | 0, no file produced | 1, file produced |
| `rt_dir_walk` | 0 entries | 2150 entries |
| `rt_dir_create` | 0, nothing created | 1, tree created |
| `rt_dir_create_all` | **1, and created `.../zXXXXXXXX...` on disk** | 1, correct path |
| `rt_dir_remove_all` | -256 (not even a bool) | 1 |
| `rt_panic` | `PANIC: assertion failed: x > 0XXXXXX...` | `PANIC: assertion failed: x > 0` |

`rt_dir_create_all` is the one to remember: it returned **success** while
creating a directory whose name carried 64 bytes of trailing heap garbage. The
`-1` / `0` / empty-string results elsewhere are the reason the class stayed
silent for so long -- every one of them is also a legitimate "file not found"
answer, so no caller could tell an ABI defect from a missing file.

### Corrections to this document

* The C-internal caller counts above ("rt_dir_create 4, rt_dir_walk 3") do not
  survive contact with the source. Actual counts, audited per symbol:
  `rt_dir_create` 1 real + 5 in `platform/test_*.h`; `rt_dir_remove_all` 1 real
  (`rt_dir_delete`) + 4 test; `rt_dir_create_all` 1 (`rt_mkdir_p`);
  `rt_dir_exists` 1; `rt_file_fsync` 2. `rt_dir_walk` has **none**.
  Where a caller passes a genuine C string, the body was kept as a
  `*_cpath` worker and the `rt_*` entry point became a thin converting wrapper.
* `rt_mkdir_p` was listed as a row but has **no `RuntimeFuncSpec`** -- the
  compiler never calls it. It keeps its C-string signature over the shared
  worker, and it was never in the baseline.

### Two gaps in the gate, found while closing this

1. **Header definitions are invisible.** The gate parses only
   `src/runtime/*.c` at depth 1. `rt_dir_create` and `rt_dir_remove_all` are
   defined in `src/runtime/platform/unix_common.h` and
   `platform/platform_win.h`, pulled into `runtime.c`'s translation unit by
   `#include "platform/platform.h"`. The gate never saw those definitions.
2. **Arity-only comparison misses same-arity defects.** `rt_file_sync` (in
   BOTH `runtime.c` and `runtime_legacy_core.c`) already had arity 2 and was
   never flagged -- but it did `(void)path_len;` and used the pointer as a C
   string, the identical defect. Both copies were fixed here. A parameter-TYPE
   check would catch that class; a RETURN-type check would catch
   `rt_file_read_text`, which still returns `char*` where the compiler declares
   `I64` (a RuntimeValue) -- an open, separate divergence.

### Verification

* Freshly rebuilt `src/compiler_rust/target/release/simple` (`cargo build
  --release`, 3m22s, no errors). A stale prebuilt `libruntime_sffi_c.a` is what
  masked this class originally, so nothing prebuilt was trusted.
* `nm` on that binary: **exactly one** definition of each of the 15 symbols
  survives -- the release lane links only the Rust SFFI, confirming the C copies
  serve the AOT/native lanes and must be proven at the C level, which is what the
  reproduction harness does.
* Simple-level probe over slice- and concatenation-built paths agrees in the
  JIT/native and interpreter lanes.
* `sh scripts/check/check-extern-abi-signatures.shs` ->
  `PASS -- 470 symbols checked, 0 baselined, 0 new`.

`-z muldefs` was deliberately left in place: removing it is the multi-day
re-layering described above, and it is not what made this class silent -- the
missing gate was.
