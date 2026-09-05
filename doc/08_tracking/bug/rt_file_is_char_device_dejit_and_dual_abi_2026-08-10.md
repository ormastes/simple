# `rt_file_is_char_device`: whole-repo de-JIT (stale seed) + dual-ABI wrong answer

**Date:** 2026-08-10
**Status:** RED (defect B); defect A fixed in source, stale in deployed binary
**Found while:** unblocking the spec-vacuity census driver
(`scripts/check/census-spec-vacuity.spl`, landed `bbe4682d52b`), which could not
produce a census because it dropped to the interpreter and was SIGTERMed.

## Defect A — every consumer of `std.nogc_sync_mut.io_runtime` de-JITs

`io_runtime.spl` declares the extern at

- `src/lib/nogc_sync_mut/io_runtime.spl:52` — `extern fn rt_file_is_char_device(path: text) -> bool`
- `src/lib/nogc_sync_mut/io_runtime.spl:249` — `pub fn is_char_device`

The JIT declares an import for **every** extern in a module regardless of
reachability (`src/compiler_rust/compiler/src/codegen/jit.rs:160`,
`first_unresolved_import`). So *any* import from `io_runtime` — the most-used
stdlib module in the repo — drops the whole program to the interpreter.

Reproduced with a program that only imports `file_read`:

```
[jit-fallback] unresolved external symbol 'rt_file_is_char_device':
  whole module dropped to the interpreter (expect ~100-1000x slowdown).
```

### Root cause: a 20-hour source window, and a deployed binary inside it

| what | where | landed |
|---|---|---|
| `.spl` extern declared | `src/lib/nogc_sync_mut/io_runtime.spl:52` | `78dbaff5d7c` 2026-08-08 08:54 |
| JIT symbol manifest entry | `src/compiler_rust/common/src/runtime_symbols.rs:967` | `b68d7a2d461` 2026-08-10 04:29 |
| deployed seed built | `bin/release/x86_64-unknown-linux-gnu/simple` | 2026-08-09 04:50 |

The Simple-layer extern shipped ~20 h before the symbol was added to
`RUNTIME_SYMBOL_NAMES`, which is what `build.rs` turns into
`RUNTIME_SYMBOL_ENTRIES` (`src/compiler_rust/runtime/build.rs:102-115`) and what
`jit.rs:388-390` consults. The deployed seed was built inside that window, so it
has the extern but not the symbol.

**Source on `main` is already correct.** Nothing to change. The deployed binary is
stale. Redeploying `bin/release/**` is out of scope here (hard constraint), so it
must be redeployed by the bootstrap lane.

Corroboration that this was already known and blocking another lane:
`scripts/check/check-engine2d-jit-timing.shs:10-11,50-51,69` explicitly reports
its JIT/interpreter split as unobtainable "blocked by `rt_file_is_char_device`
unresolved symbol".

## Defect B (NEW, RED) — two incompatible definitions of the same symbol

Once the symbol *does* resolve, the answer is wrong. With a seed that has the
manifest entry (`src/compiler_rust/target/release/simple`):

```
c_zero=false   c_null=false   c_tty=false      # JIT   — all three are WRONG
zero=true      null=true                       # interp — correct
f_readme=true  d_src=true                      # is_file / dir_exists are fine
```

`/dev/zero`, `/dev/null`, `/dev/tty` are all character devices. The extern-bool
path is not broadly broken — only this symbol is.

There are **two** definitions with **incompatible ABIs**:

| definition | signature |
|---|---|
| `src/runtime/runtime.c:963` | `int rt_file_is_char_device(const char* path)` — NUL-terminated C string, **1 arg** |
| `src/runtime/runtime_native.c:7618` | same C-string ABI |
| `src/compiler_rust/runtime/src/value/sffi/file_io/metadata.rs:40` | `(path_ptr: *const u8, path_len: u64) -> bool` — **2 args** |

The compiler declares the two-arg form
(`src/compiler_rust/compiler/src/codegen/runtime_sffi.rs:1838`,
`&[I64, I64] -> &[I8]`) and decomposes `text` into (ptr, len)
(`src/compiler/50.mir/text_extern_abi.spl:69`). If the C definition wins at link
time it receives a **non-NUL-terminated** pointer and ignores the length, stats a
garbage path, and returns `false` — exactly the observed constant-false. This is
the `-z muldefs` hazard: duplicate symbols are silent, not fatal.

**Fix direction:** one definition per symbol. Either give the C runtime the
`(ptr, len)` ABI to match `runtime_sffi.rs:1838`, or drop the C definitions and
let the Rust SFFI one be the only provider. Do not leave both.

Note the Rust implementation itself is correct (`metadata.rs:38-60`,
`std::fs::metadata(...).file_type().is_char_device()`), so this is purely a
duplicate-definition / ABI-selection defect, not a logic bug.

## Defect C — `SIMPLE_TIMEOUT_SECONDS` not reaching the monitor: NOT REPRODUCIBLE

The monitor **does** read it, live, from the victim's own `/proc/<pid>/environ`:
`scripts/resource/kill_simple_monitor.shs:103-118` (`cpu_budget_secs`), with an
explicit `0` disabling the CPU guard at line 111. The running monitor (PID 2015,
started 2026-08-09 ~09:00 UTC) postdates that code (file mtime 2026-08-09 04:57).
The earlier report predates the fix. No action.

Caveat for future triage: an `exit 143` with no verdict line at high RSS is
**earlyoom**, not the monitor — a 1529-spec census run died at 47.9 s / 644 MB,
well under the 60 s CPU budget.

## Bounded proof that the driver works once the symbol resolves

```
SIMPLE_TIMEOUT_SECONDS=0 src/compiler_rust/target/release/simple run \
  scripts/check/census-spec-vacuity.spl test/01_unit/os

REPORT -- 687 file(s) scanned, 0 deduped VTM finding(s), 0 raw; 0 deduped SHADOW file(s)
EXIT=0   WALL=59.48s   MAXRSS=1051900kB
```

No `[jit-fallback]` line on stdout or stderr, real verdict line, exit 0. With the
deployed stale seed the same module de-JITs before it starts.

---

## Re-verification 2026-08-17 (io lane) — BOTH defects now GREEN by content

Classified by CONTENT (grep of current source), not by commit ancestry.

**Defect B (dual ABI) — FIXED.** The incompatible NUL-terminated `const char*`
copy is gone from `src/runtime/runtime_native_gpu_stub.c`; that file now carries
only a comment at lines 24-35 explaining the removal and forbidding its return.
The two surviving C definitions agree with the Rust canonical one on the
two-argument `(ptr, len)` form:
- `src/runtime/runtime.c:1172` — `int rt_file_is_char_device(const uint8_t* path_ptr, uint64_t path_len)`
- `src/runtime/runtime_native.c:8520` — same signature
- `src/runtime/runtime.h:833` — same prototype
- `src/compiler_rust/runtime/src/value/sffi/file_io/metadata.rs:275` — `pub unsafe extern "C" fn rt_file_is_char_device(path_ptr: *const u8, path_len: u64) -> bool`

**Defect A (whole-repo de-JIT) — no longer reproduces on the DEPLOYED binary.**
`rt_file_is_char_device` is present in
`src/compiler_rust/common/src/runtime_symbols.rs` (1 occurrence), and the
deployed seed (`bin/release/x86_64-unknown-linux-gnu/simple`, 59536728 bytes,
mtime 2026-08-16 22:59:37) no longer drops to the interpreter on an
`std.io_runtime` import:

```
$ cat /tmp/probe3.spl
use std.io_runtime.{file_exists}
fn main() -> i64:
    print(file_exists("/etc/hostname"))
    return 0
$ SIMPLE_RUST_SEED_WARNING=0 SIMPLE_EXECUTION_MODE=jit bin/simple run /tmp/probe3.spl
true
```

No `[jit-fallback] unresolved external symbol 'rt_file_is_char_device'` line on
stdout or stderr, and the answer is correct. The 2026-08-10 staleness window has
been closed by the newer deployed seed.

Recommend: close. No change was needed in `src/lib/nogc_sync_mut/io_runtime.spl`
— its declaration at line 52 was always the correct one.
