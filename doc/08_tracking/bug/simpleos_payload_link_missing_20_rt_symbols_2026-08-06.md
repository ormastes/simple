# SimpleOS Simple payload fails to link: 20 `rt_*` symbols exist in no target runtime

Status: OPEN
Found: 2026-08-06, Lane S1 of
`doc/03_plan/os/simpleos/toolchain_selfhost_bootstrap_plan.md`
Blocks: S1 (cross Simple payload), and therefore S2/S3/S4/P1/P2.

## Summary

`bin/release/x86_64-unknown-simpleos/simple` cannot be produced. The
`native-build` compile stage succeeds; the **link** stage fails with 20
undefined `rt_*`/runtime symbols. The SimpleOS target has no runtime component
that defines them:

- the pure-Simple `simple-core` archive **declares** them `extern fn` (it
  expects a C runtime to supply them), and
- the SimpleOS C-side runtime shim defines only 21 symbols, none of which are
  the 20 required.

This is a genuine missing-implementation gap, not a build-wiring mistake.

## Exact repro

Seed used (D1 route-around; the deployed binary SEGVs on `native-build`):

```
SIMPLE_BUILD_COMPILER=/home/ormastes/dev/pub/simple/src/compiler_rust/target/bootstrap/simple
  sha256 13ebe5dd22f0cabf37ab72e3b6f89b9f6271682587f848a205b5252ac4dc2e2d
```

```bash
SIMPLE_BOOTSTRAP=1 SIMPLE_NO_STUB_FALLBACK=1 \
SIMPLE_BUILD_COMPILER=/home/ormastes/dev/pub/simple/src/compiler_rust/target/bootstrap/simple \
  sh scripts/os/simpleos-native-build.shs
```

Underlying command (from the script):

```bash
SIMPLE_SIMPLE_CORE_PATH=build/os/simple-core-simpleos/libsimple_runtime.a \
SIMPLE_BOOTSTRAP=1 SIMPLE_NO_STUB_FALLBACK=1 <seed> native-build \
  --source src/compiler --source src/lib --source src/app \
  --backend cranelift --runtime-bundle simple-core --entry-closure \
  --entry src/app/simpleos_tool/main.spl \
  --target x86_64-unknown-simpleos \
  -o bin/release/x86_64-unknown-simpleos/simple
```

Step `[0/2]` (target Simple-core runtime) SUCCEEDS
(`simple_core_archive_complete=true`). Step `[1/2]` fails:

```
Freestanding unresolved symbol check: 511 unexpected symbol(s)
Freestanding unresolved precheck deferred to linker: 505 candidate symbol(s)
Build failed: link failed: ld.lld: error: undefined symbol: rt_string_new_literal
```

## The 20 undefined symbols

```
rt_bytes_to_text                  rt_text_to_bytes
rt_clear                          rt_transient_array_scope_begin
rt_env_get_i64                    rt_transient_array_scope_end
rt_env_remove                     rt_transient_array_scope_pause
rt_file_is_regular_no_follow      rt_transient_heap_promote
rt_native_cmp                     rt_value_as_float
rt_pop                            sigpending
rt_sort                           simple_contract_check
rt_string_new_literal             spl_wffi_call_i64
rt_text_cmp_any
rt_text_slice_audit_note_range
```

Grouped: core array ops (`rt_sort`, `rt_pop`, `rt_clear`, `rt_native_cmp`),
the transient-heap allocator protocol (`rt_transient_array_scope_{begin,end,
pause}`, `rt_transient_heap_promote`), text/bytes conversion, env access, the
WFFI bridge (`spl_wffi_call_i64`), and the contract checker.

## Why nothing defines them

| Component | Path | Defines | Verdict |
|---|---|---|---|
| pure-Simple core archive | `build/os/simple-core-simpleos/libsimple_runtime.a` (18 members, all `mod_0.o`) | 379 `T` | declares the 20 as `extern fn`, defines 0 of them |
| SimpleOS C runtime shim | `src/os/libc/simpleos_simple_runtime.c` (230 lines) → `libsimple_runtime_compat.a` | 21 `T` | defines **0** of the 20 (verified by `nm`) |
| sysroot libs | `libsimpleos_c.a`, `libm.a`, `libc++.a` | — | define 0 of the 20 |
| host C runtime | `src/runtime/runtime_native.c` | defines all 20 | **never cross-compiled for SimpleOS** |

Evidence the simple-core side only declares them — both symbols my first grep
counted as "present" are `extern fn` declarations, not definitions:

```
src/runtime/simple_core/core_string.spl:44:
  extern fn rt_text_slice_audit_note_range(src: i64, src_len: i64, begin: i64, finish: i64) -> i64
src/runtime/simple_core/core_process.spl:35:
  extern fn sigpending(set_ptr: i64) -> i64
```

What is proven: **`src/runtime/runtime_native.c` is the only component that
implements these 20, and no archive on the SimpleOS link line defines any of
them** (full 20-symbol `nm` sweep across every `build/os/sysroot/lib/*.a`
returned zero hits in every library).

**This is a REGRESSION, not a never-worked gap.** Plan section 0 records the
`simpleos_tool` payload linking and running in-guest at `fe9fbd8c2285`. Neither
of the obvious suspects changed since:

- `src/os/libc/simpleos_simple_runtime.c`: 231 lines then, 230 now — no
  functional commits in between.
- `scripts/os/simpleos-native-build.shs`: unchanged, and already used
  `--runtime-bundle simple-core` with the same `--entry` at that commit.

So the regression is upstream of both: the **entry closure of
`src/app/simpleos_tool/main.spl` grew** — `src/lib`/`src/compiler` code newly
reachable from it now calls 20 `rt_*` the SimpleOS runtime never provided.
Root cause is NOT yet isolated to a specific commit; the bisect over
`fe9fbd8c2285..HEAD` for `src/lib` + `src/runtime/simple_core` is the next step
and has not been run.

**`--runtime-bundle` is not the cause.** The seed supports three bundle modes
(`auto`, `simple-core`, `core-c-bootstrap`) and the script hardcodes
`simple-core`. Re-running the identical `native-build` with
`--runtime-bundle core-c-bootstrap` fails with **the same 20 undefined symbols**
and the same first error (`rt_string_new_literal`). So no available bundle mode
supplies a C runtime that covers them.

Note also `scripts/os/simpleos-native-build.shs:129` copies the simple-core
archive over `build/os/sysroot/lib/libsimple_runtime.a`, which `sysroot.shs:131`
had made a copy of the 21-symbol compat shim. So the compat shim is not on the
link line at all — but restoring it does **not** fix this, since it defines none
of the 20.

## Fix options (not attempted — out of Lane S1 scope)

1. **Preferred:** extend `src/os/libc/simpleos_simple_runtime.c` to cover the 20,
   or cross-compile the relevant parts of `src/runtime/runtime_native.c` for
   SimpleOS and add the archive to the link.
2. Implement them in `src/runtime/simple_core/*.spl` as real Simple definitions
   instead of `extern fn` declarations.
3. ~~**Likely cheapest, and try this first:** cut the newly-reachable closure
   edge rather than write 20 primitives.~~ **TESTED AND REFUTED — 2026-08-06.
   See "Closure-cut hypothesis is dead" below. Do not spend more time here.**

Deliberately NOT done here: fabricating stubs. `SIMPLE_NO_STUB_FALLBACK=1` and
the compiler's own `simpleos_check_no_fabricated_rt_stubs` guard exist to forbid
exactly that, and a stubbed `rt_sort`/transient-heap protocol would produce a
payload that links and then corrupts memory in-guest. The transient-heap scope
trio in particular is an all-or-nothing protocol.

## Closure-cut hypothesis is dead (tested 2026-08-06)

The "cut the closure edge" theory above was the cheapest fix and was tested
directly. **It does not work, and it cannot work.** Two independent results:

### 1. Removing the only new import edge changed nothing

`main.spl` is the *only* file in `src/app/simpleos_tool/` that changed since
`fe9fbd8c2285` (12 insertions, 13 deletions). The change swapped two direct
`extern fn` decls for module imports:

```
-extern fn rt_cli_get_args() -> [text]        +use app.io.args_ops.{get_args}
-extern fn rt_env_set(key: text, value: text) +use app.io.env_ops.{env_set}
```

`app.io.env_ops` is a star-import facade (`export use
std.nogc_sync_mut.io.env_ops.*`), which looked like the classic hub-import
pathology. Reverting that edge to the original `extern fn rt_env_set` and
rebuilding produced a **byte-for-byte identical failure**: `511 unexpected
symbol(s)`, the same 20 undefined symbols, same first error. The edge is not
the cause.

(Both externs used at `fe9fbd8c2285` still resolve today — `rt_cli_get_args` in
`libsimpleos_c.a` *and* simple-core, `rt_env_set` in simple-core. So runtime
coverage for the original closure never regressed.)

### 2. Five of the 20 are demanded by the runtime archive itself

Attributing every undefined reference to its demanding object shows the demand
does not come only from the payload closure:

| Demanded by | Symbols |
|---|---|
| **`libsimple_runtime.a` itself** (simple-core) | `sigpending` (← `rt_signal_check`), `rt_native_cmp` (← `rt_native_eq_inner`, `rt_slice`), `rt_string_new_literal` (← `rt_platform_name`), `rt_text_slice_audit_note_range` (← `rt_slice`) |

**`sigpending` is a libc gap, not a runtime gap.** It is the only one of the 20
that is a plain POSIX function rather than an `rt_*`/`spl_*` primitive, it is
confirmed `MISSING` from `libsimpleos_c.a`, and it belongs in
`src/os/libc/simpleos_signal.c` beside the `sigprocmask`/`sigemptyset` family
already declared in `include/signal.h:75-86`. It is a ~10-line syscall wrapper
and can be closed independently of the runtime port. So the true split is
**19 runtime-port items + 1 cheap libc item**.
| `src/compiler` frontend/backend | `rt_sort`, `rt_pop`, `rt_clear`, the transient-heap trio + `rt_transient_heap_promote`, `rt_env_get_i64`, `rt_env_remove`, `rt_value_as_float`, `rt_file_is_regular_no_follow`, `simple_contract_check`, `spl_wffi_call_i64`, `rt_text_cmp_any` |
| `src/lib/common` | `rt_text_to_bytes`, `rt_bytes_to_text`, `rt_string_new_literal`, `rt_text_cmp_any` |

**No payload-closure edit can remove the first row** — that is the Simple-core
runtime's own Simple code calling C primitives that no SimpleOS-side component
defines. The second row is a compiler frontend/backend
(`_FlatAstBridge__module_assembly__parse_and_build_module_scoped`,
`_Ast__module_state__ast_gen_harden_*`), which is irreducible for a payload
whose entire purpose is compiling Simple on the guest.

**Conclusion: the closure growth is legitimate and irreducible. This is a real
missing-implementation gap and needs option 1 or 2, not an import cleanup.**

## Feasibility probe for option 1 (cross-compiling the real runtime)

Measured 2026-08-06, not yet acted on. `src/runtime/runtime_native.c` (9,356
lines) is **much closer to cross-compilable than expected** — it is not a
host-only file:

```bash
clang --target=x86_64-unknown-none-elf -ffreestanding -nostdlib -nostdlibinc \
  -fno-builtin -mno-red-zone -fno-stack-protector -O1 -D__simpleos__=1 \
  -ferror-limit=0 -isystem src/os/libc/include -fsyntax-only \
  src/runtime/runtime_native.c
```

Total gap is **3 missing headers** (`netdb.h`, `arpa/inet.h`, `netinet/tcp.h`)
plus a small set of declarations absent from existing SimpleOS headers:
`sig_atomic_t`, `PTHREAD_CREATE_DETACHED`, `SO_BROADCAST`, `TCP_NODELAY`,
`INET_ADDRSTRLEN`, `struct addrinfo`/`EAI_*`, and decls for `fdopen`, `fsync`,
`pread`, `pwrite`, `strcasestr`, `inet_ntop`, `inet_pton`, `getaddrinfo`,
`freeaddrinfo`, `pthread_attr_setdetachstate`.

Of those, `libsimpleos_c.a` **already defines** `popen`, `pclose`,
`pthread_attr_setdetachstate`, `pthread_attr_init`. Genuinely missing
implementations: `fdopen`, `fsync`, `pread`, `pwrite`, `strcasestr`,
`inet_ntop`, `inet_pton`, `sigpending`, `getaddrinfo`/`freeaddrinfo` — all but
the last pair are thin syscall or pure-string wrappers. SimpleOS has no DNS
resolver, so `getaddrinfo` should resolve numeric addresses for real and return
`EAI_NONAME` otherwise (a truthful failure, not a fabricated success).

### The transient-heap protocol is portable, NOT blocked

`rt_transient_array_scope_{begin,end,pause}` and `rt_transient_heap_promote`
are the memory-management-critical group, but the **real implementations exist
in `src/runtime/runtime_native.c`** and are covered by the cross-compile probe
above. They must be ported *wholesale* and never approximated — but they are
not an open gap.

### Hard blocker inside option 1

**`rt_pop`, `rt_clear`, and `rt_env_remove` are defined in NO C source
anywhere** (`grep -rn` over all of `src/runtime/` and `src/os/libc/` returns
nothing). They exist only in the Rust runtime,
`src/compiler_rust/runtime/src/value/collections.rs`. Cross-compiling
`runtime_native.c` therefore covers 17 of the 20, not all 20. Porting these
three means reimplementing them in C against the *same* array representation
`runtime_native.c` uses — a mismatched layout would link cleanly and corrupt
silently, which is exactly the failure mode the no-stub rule exists to prevent.

### Packaging requirement

Build one `.o` per source file and `ar rcs` them into a **separate** archive
(e.g. `libsimple_runtime_native.a`); do not partial-link (`ld -r`) into one
blob. Archive-member granularity is what keeps the socket/DNS-dependent code
from being dragged in by an unrelated `rt_sort` reference — the same lesson as
`simpleos_libc_leaks_simple_runtime_syms_2026-08-06.md`.

Note the new archive must **not** be named `libsimple_runtime.a`:
`scripts/os/simpleos-native-build.shs:129` overwrites that exact path with the
simple-core archive on every run.

Per Lane S1's instruction ("if the bootstrap seed also fails, file the exact
error against D1 and stop the lane"), the lane is stopped here.

## Related defects found on the way

- **D1 confirmed empirically.** `release/x86_64-unknown-linux-gnu/simple` is
  sha256 `04a38e21d6fbd86149d46d3ee2d761349f8ad29b02c5037a8eb589b6a1b9e4e0` —
  byte-identical to the artifact named in
  `deployed_selfhost_env_set_miscompile_segv_2026-07-14.md` — **and** it is the
  FIRST entry in this script's compiler-discovery glob, so the default path
  selects the known-SEGV binary.
- **`bin/release/x86_64-unknown-linux-gnu/simple` is a Rust seed copy**, not a
  self-hosted binary: `--version` prints "bootstrap seed only". The "deployed
  self-hosted compiler" does not currently exist.
- **NEW: `bootstrap/stage3/x86_64-unknown-linux-gnu/simple` core-dumps** on
  `native-build --target x86_64-unknown-simpleos --help` (sha256
  `48a12b4f8fe2208ed844ac49ecadfbd3e70b02c06a573f438c1144f5483b577d`). It passes
  the seed-banner guard, so it was a candidate builder.
- **NEW (fixed here): fail-open probe gate.** The script's `--target` probe used
  `|| true` and matched only "unknown"/"unrecognized" in the output. A crashing
  compiler emits no output, so it PASSED the gate — the core-dumping stage3
  binary above would have been accepted and used. Now rejected on rc >= 128.
