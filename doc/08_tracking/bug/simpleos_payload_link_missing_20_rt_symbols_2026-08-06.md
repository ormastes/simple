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
3. **Likely cheapest, and try this first:** the fix is probably *not* 20 new
   implementations. Since this is a regression from closure growth, identify
   which newly-reachable module dragged these in and cut that edge —
   `simpleos_tool` is the *focused* payload by design, and a closure that needs
   the WFFI bridge and the transient-heap protocol suggests it now accidentally
   reaches general-purpose `src/lib` code. Start with
   `nm -u .simple/native-objects-*/mod_*.o | grep rt_sort` to find the
   referencing module, then bisect `fe9fbd8c2285..HEAD` over `src/lib` and
   `src/runtime/simple_core`.

Deliberately NOT done here: fabricating stubs. `SIMPLE_NO_STUB_FALLBACK=1` and
the compiler's own `simpleos_check_no_fabricated_rt_stubs` guard exist to forbid
exactly that, and a stubbed `rt_sort`/transient-heap protocol would produce a
payload that links and then corrupts memory in-guest. The transient-heap scope
trio in particular is an all-or-nothing protocol.

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
