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

## Return-type divergence closed, and the gate extended (2026-08-10, part 2)

`rt_file_read_text` was the last known open row: the compiler declares
`RuntimeFuncSpec::new("rt_file_read_text", &[I64, I64], &[I64])`
(`runtime_sffi.rs:1852`) -- the result is a **RuntimeValue** -- while both C
copies returned a raw `const char*` straight out of `spl_file_read`.

**The compiler's declaration is the authority for RETURNS as well as
parameters,** for the same reason: it is the only layer that all three
implementations are compiled against, the canonical Rust definition
(`file_io/file_ops.rs:253 -> RuntimeValue`) already agrees with it, and every
Simple-side caller spells the result as `text`. The C copies were out of step.

### Reproduction

Against the real translation units (`runtime.c`, `runtime_native.c`,
`runtime_legacy_core.c`, `-z muldefs`), calling through the ABI the compiler
emits -- `int64_t rt_file_read_text(const uint8_t*, uint64_t)` -- with a
**non-NUL-terminated** path buffer padded with `X`:

```
before:  [simple-runtime][error] rejected invalid array handle before dereference;
                                 probable compiler/FFI ABI mismatch (value_bits=0x00005fcc10dbb530)
         raw=0x00005fcc10dbb530   read_len=0        <- a 4-byte file read as EMPTY
         control (rt_string_new "hello") = 0x...551  len=5
```

The returned word is a bare heap address with no tag; the runtime's own handle
validator says so. `read_len=0` is the reason this stayed silent: it is also
the answer for an empty file and for a missing one.

After the fix, all three outcomes are distinguishable, in **all three C link
orders** (muldefs makes link order pick the winner):

| case | raw | class | len |
|---|---|---|---|
| existing file | `0x...541` | str | 4 (`abc\n`) |
| empty file | `0x...e31` | str | 0 |
| missing file | `0x0000000000000003` | NIL | — |

Returning NIL for a missing path also required an explicit openability probe:
`spl_file_read` returns `""` (not NULL) when the open fails, so the C lane
could not distinguish missing from empty at all, and Simple's `... ?? ""` arm
was dead. The Rust definition returns NIL; the C copies now do too.

There are **zero** C-internal callers of `rt_file_read_text`, so the change is
closed. `runtime.h` was updated to match.

### Gate extension: RETURN types

`scripts/check/check-extern-abi-signatures.shs` now compares a return **ABI
class** -- `void` / `int` / `float` / `ptr` / `multiN` -- across the compiler
declaration and every C and Rust definition, alongside the existing arity
check. Rows are emitted as `<sym>  ret:<decl>  ret:<def>  <file>` into the same
baseline ratchet.

Both gaps recorded below are also closed:

* **Header coverage.** The scan now reads `src/runtime/**/*.h` at any depth
  (vendored trees pruned) as well as `src/runtime/*.c`. Pure declarations are
  still skipped, because the C extractor requires `{` on the declarator line.
  Four **per-location** positive controls run on the real tree and are fatal
  if any yields zero: `src/runtime/*.c` = 1278 defs, `src/runtime/**/*.h` = 79,
  `src/runtime/platform/*.h` = 79, Rust SFFI = 399. The header path immediately
  produced real rows (`rt_dir_list` in both `unix_common.h` and
  `platform_win.h`) -- previously invisible.
* **Alias return consistency.** `codegen/instr/calls.rs` and
  `codegen/llvm/functions/calls.rs` rewrite call names before emission
  (`rt_file_read_text` -> `rt_file_read_text_rv`). Neither states a return
  type, so there is nothing there to compare directly; instead the gate asserts
  that both ends of every alias pair declare the same result class (6 pairs).

Selftest is still fatal and runs before every scan, now with 7 fixtures: a
return-type fixture (`bad_ret_defs.c`, same arity on purpose, so only the
return check can see it) and a header-location positive control
(`platform/good_hdr_defs.h`, which must be extracted AND must not flag).

Verdict: `PASS — 470 symbols checked, 33 baselined, 0 new`.

### What the gate still cannot catch

* **Semantics behind an identical signature.** `rt_file_sync` had the right
  arity and still used the pointer as a C string with `(void)path_len;`. That
  was found by hand and nothing in this gate would find the next one.
* **`ptr` vs `int` is a SEMANTIC signal, not an ABI one.** On every supported
  target a pointer and an `I64` share the return register, so the 26 `ret:int`
  vs `ret:ptr` rows are all ABI-compatible. `rt_file_read_text` was fatal for a
  semantic reason -- the value was consumed as a *tagged* RuntimeValue. The
  gate cannot tell a tagged value from a raw address; the baseline records the
  human triage. Eight of those rows (`rt_bytes_from_raw`, `rt_bytes_to_text`,
  `rt_dir_list`, `rt_dir_walk`, `rt_env_cwd`, `rt_platform_name`,
  `rt_process_run`, `rt_process_run_timeout`) are the **same class as
  rt_file_read_text and are still open** -- their Rust definitions return
  `RuntimeValue` while the C copies return `char*`.
* **Return WIDTH inside `int`.** `I8` vs `I32` vs `I64` is not compared, so a
  callee that writes only the low 32 bits where the caller reads 64 is invisible.
* **Parameter TYPES.** Only parameter *count* is compared. A `const char*`
  where a `uint64_t` is declared, at the same arity, is still invisible.
* **Multi-line `RuntimeFuncSpec::new(` forms** (~14 of them) are not parsed by
  the line-oriented declaration extractor, so those symbols are simply absent
  from the comparison rather than wrongly compared.
* **Only `rt_*` symbols**, and only definitions matching the accepted C
  declarator shape (`{` on the declarator line, column 0, non-`static`).
* The pure-Simple LLVM backends carry their own stale extern lists
  (`llvm_backend.spl:388` `declare ptr @rt_file_read_text(ptr)`,
  `llvm_lib_translate.spl:279`), which still spell the whole file-I/O family
  with a single `ptr` parameter. The gate does not read those files. Whether
  they are reachable was not established here -- filed as a separate follow-up,
  not claimed as fixed.

### Two gaps in the gate, found while closing this (both now CLOSED -- see above)

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

## Group B1 closed, Group A audited, B2 corrected (2026-08-10, part 3)

### Group B1 -- all 8 symbols resolved

Method per symbol, identical to the Class-1 parameter sweep and to
`8b606950a20`: compile the real translation units (`runtime.c`,
`runtime_native.c`, `runtime_legacy_core.c`, `runtime_process.c` and the rest of
the native lane), call each definition through the ABI the compiler actually
emits, with a **non-NUL-terminated** path buffer padded with `X`, and decode the
returned word as a RuntimeValue. Repeated in **all three C link orders**, since
`-z muldefs` makes link order pick the winner. `rt_string_new("hello")` runs as
a positive control in every invocation and must read back `tag=1 STR len=5`.

The decoder distinguishes what the old `len=0` result could not: `tag=1` is a
correctly tagged heap value, `tag=0` is a raw address, `3` is NIL.

| symbol | before | after | verdict |
|---|---|---|---|
| `rt_env_cwd` | `tag=0` raw address; handle validator fires | `tag=1 STR len=98` | REAL |
| `rt_platform_name` | `tag=4` -- a `.rodata` pointer, not even 8-aligned | `tag=1 STR "linux"` | REAL |
| `rt_bytes_to_text` | **SIGSEGV** in the link order where the `runtime.c` copy wins | `tag=1 STR "hello"` all orders | REAL |
| `rt_dir_walk` | `tag=0`, `array_len=0` on a **3-file** fixture | `tag=1 array_len=3` | REAL |
| `rt_dir_list` | **SIGSEGV on every call, every link order**, existing dir and missing dir alike | `tag=1 array_len=2` | REAL |
| `rt_bytes_from_raw` | `tag=1 array_len=5` | unchanged | spelling only |
| `rt_process_run` | `tag=1 array_len=3` | unchanged | spelling only |
| `rt_process_run_timeout` | `tag=1 array_len=3` | unchanged | spelling only |

**Five of eight were real defects.** The three that were not are recorded as
such with the measurement that shows it, rather than being waved through --
`ptr` and `I64` share the return register, so nothing but a per-symbol
measurement can tell the two cases apart.

`rt_dir_list` deserves its own note: it is the first row in this whole family
that the **arity** check could never have found. The compiler declares
`(path_ptr, path_len) -> RuntimeValue`; the only C definition was the platform
header's `const char** rt_dir_list(const char* path, int64_t* out_count)`. Both
have arity 2. The compiler passed a path LENGTH where that body dereferenced an
out-parameter and wrote through it. Only the new RETURN-class check
(`const char**` vs `I64`) surfaced the row at all.

Revert-proofs were taken by rebuilding the pre-change source from its own commit
via `git archive`, not from memory.

### Group A -- audited, and it splits three ways

Recorded in full in the baseline header. Summary: `rt_array_set` and
`rt_channel_send` need the **C definition** fixed (the Rust definitions already
agree with the compiler); `rt_invlpg` and `rt_write_cr3` need the **compiler
declaration** fixed to `&[]` (no Rust counterpart, every Simple declaration and
every caller says void); `rt_file_close` is a **real defect with a live
consumer** -- `infra/file_io.spl:439` does `val success = rt_file_close(fd)`
while both definitions return void -- and needs the definitions fixed; `rt_exit`
is benign, its Rust signature is `-> !` and the gate misreads the never type as
a value class. Batch-assuming any single direction would have been wrong for
most of the group.

### Group B2 -- the "no counterpart" note was wrong

Two of the four residual rows are not merely unmeasured, they look like open
defects of exactly the class this campaign has been closing:
`rt_coverage_dump_sdn` and `rt_host_gpu_queue_last_payload_text` are declared
`-> &[I64]` (RuntimeValue) and return raw C strings in **every** implementation.
`rt_cli_get_args` / `rt_get_args` do have RuntimeValue-returning Rust
counterparts and are probably spelling-only, but that has not been measured.
Details in the baseline header. None of these were upgraded to "fine".

### The pure-Simple LLVM backends: REACHABLE, and one call site is live-wrong

The earlier follow-up ("whether they are reachable was not established") is now
established: **they are reachable**, and there are THREE such lists, not two.

* `llvm_backend.spl:366 generate_runtime_declarations_for_target` is called at
  `llvm_backend.spl:285` and its output is prepended to **every** LLVM IR module
  the pure-Simple backend emits; `build_native.spl` and
  `build_native_pipeline.spl` both import it.
* `llvm_lib_translate.spl:268 declare_runtime_functions` is the LLVM-C-API twin.
* `_MirToLlvm/asm_constraints_helpers.spl:145+ emit_runtime_declarations` is
  called from `_MirToLlvm/core_codegen.spl:183`, i.e. inside `translate_module`.

A stale `declare` alone is inert -- LLVM will not emit a call for it. But
`asm_constraints_helpers.spl:400` **emits an actual call**:

```
    self.builder.emit("  call void @rt_panic(ptr {ptr_name})")
```

one argument, while `rt_panic` was converted to `(ptr, len)` by the Class-1
parameter sweep. That is a live ABI mismatch in emitted code, not just a stale
declaration, and it is the same defect class this family exists to track. Filed
here; not fixed in this change.

The declaration lists also still spell the file-I/O family with a single `ptr`
(`declare ptr @rt_file_read_text(ptr)`, `declare void @rt_file_close(ptr)`,
`declare i1 @rt_file_exists(ptr)` ...) and now also disagree on RETURN type
after the B1 fixes. **The gate should read these three files**; it currently
reads only C, headers and Rust, so the entire pure-Simple backend is outside
its coverage.

Note that `core_codegen.spl:1625` rewrites `rt_process_run` ->
`@rt_process_run_tuple` and `rt_process_run_timeout` ->
`@rt_process_run_timeout_tuple` before emission, which is why the B1 return-type
changes to those two symbols do not affect this lane.

### Process note: a declaration change needs its C call sites audited

Changing `rt_process_run_timeout` from `SplArray*` to `int64_t` left its one
C-internal call site (`rt_process_result_to_tuple`, `runtime_native.c`) passing
an integer where a pointer was expected. Under `-Werror=int-conversion` that
fails to compile `runtime_native.c`, which breaks the LLVM native-link step of
every native build; it is only a warning by default, which is how it reached
origin, and two sessions misdiagnosed the result as a duplicate-symbol
collision. Fixed in `47e5dbde80e`.

The cheap guard: compile every runtime TU with
`-Werror=int-conversion -Werror=incompatible-pointer-types` after any return-type
change. Run across all eight B1 symbols it found exactly that one site, and the
current origin tree is clean under it.

## Group B2 measured and closed (2026-08-10, part 4)

The four rows the baseline carried as "unmeasured, not counterpart-less" have
now been measured, not reasoned about. Each was called through the **compiler's
emitted ABI** (`-> &[I64]`, i.e. a `RuntimeValue` word) against the real
translation units, in **three C link orders** under `-z muldefs`, with
`rt_string_new("hello")` from a **non-NUL-terminated, `X`-padded** buffer as the
positive control -- which decoded as a heap string of `len=5` in every run, so a
silent harness failure could not read as a clean result.

| symbol | measured before | verdict |
|---|---|---|
| `rt_coverage_dump_sdn` | `raw_tag=0`, decodes as a raw C string | **REAL DEFECT, fixed** |
| `rt_host_gpu_queue_last_payload_text` | `raw_tag=0`, static `char[4096]` | **REAL DEFECT, fixed** |
| `rt_cli_get_args` | `raw_tag=1`, valid RuntimeValue array | compatible, row kept |
| `rt_get_args` | `raw_tag=1`, valid RuntimeValue array | compatible, row kept |

`raw_tag` is the low 3 bits of the returned word. `TAG_HEAP` is `1`; a malloc'd
or static `char*` is at least 8-byte aligned, so it presents as `0`. That is the
whole defect: the callee returns an untagged pointer where every caller decodes
a tagged value.

### The two defects

Both are the `rt_file_read_text` class -- the two implementations agreed with
each *other* and both disagreed with the declaration, so there was no "canonical"
side to defer to. Both have live Simple consumers that spell the result `text`:

- `rt_coverage_dump_sdn` -- declared `extern fn ... -> text` in five Simple
  modules (`nogc_sync_mut/{ffi,sffi,io,test_runner}/coverage*.spl`,
  `compiler_rust/lib/std/src/tooling/coverage.spl`) and generated into test
  epilogues as `print rt_coverage_dump_sdn()`. The raw producer is now
  `rt_coverage_dump_sdn_cstr` in both `runtime_coverage_core.c` and
  `runtime/src/coverage.rs`, kept because the in-process Rust caller
  (`compiler/src/coverage.rs`) and the C selfcheck genuinely want the malloc'd
  buffer and free it with `rt_coverage_free_sdn`. The bare name now returns
  `rt_string_new(...)`. After: `raw_tag=1, len=219`.

- `rt_host_gpu_queue_last_payload_text` -- consumed by both
  `{gc,nogc}_async_mut/gpu/engine2d/host_gpu_event_queue.spl`, one of which
  stores it straight into a `last_payload_text: text` struct field. The C raw
  form is now `rt_host_gpu_queue_last_payload_text_cstr`; on the Rust side the
  `*const c_char` function no longer carries
  `#[export_name = "rt_host_gpu_queue_last_payload_text"]` -- the
  RuntimeValue-returning `_rv` function does. After: `raw_tag=1, len=0`
  (queue empty in the harness).

### Why the other two rows stay

`rt_cli_get_args` / `rt_get_args` spell the result `SplArray*` in C where
`RuntimeFuncSpec` spells it `I64`, but `rt_array_new`-built arrays are correctly
`TAG_HEAP`-tagged, so the two spellings occupy the same return register with the
same bit pattern. This was the *inference* the previous note made from the B1
sweep; it is now an execution result. Rows kept, reason upgraded from
"unmeasured" to "measured compatible".

### Gate

`PASS — 470 symbols checked, 14 baselined, 0 new` (was 16 baselined). The
ratchet, not a note, is what holds this: replanting **both** raw return types
gives `FAIL — 470 symbols checked, 2 new mismatch(es)`, and restoring them
returns the run to PASS.

All 16 runtime TUs recompile clean under `-Werror=int-conversion
-Werror=incompatible-pointer-types -Werror=implicit-function-declaration`, and
`cargo check --workspace` is clean.

### One shape left unreconciled (not an ABI divergence)

`src/app/sffi_gen.templates/simple_sffi.h:134` and the two `sffi_gen` specs
describe a *different* `rt_coverage_dump_sdn`: `bool rt_coverage_dump_sdn(const
char* path, size_t path_len)` -- a two-argument path-writing form that no
implementation provides and no caller uses. The signature gate does not read the
generator templates, so it does not see this. It is a stale generator spec, not
a live miscompile; filed here rather than fixed so the fix is not confused with
the ABI work.
