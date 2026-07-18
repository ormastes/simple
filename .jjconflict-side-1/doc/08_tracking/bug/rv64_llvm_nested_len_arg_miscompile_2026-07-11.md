# BUG: RV64 LLVM native — `text.len()` evaluates to nil (-1); hoisting into a local does NOT fix it

**Status:** FIXED in seed codegen 2026-07-11 (fix built + gate 5/5; commit pending)

## Root cause + fix (2026-07-11)

`compile_inline_len` in
`src/compiler_rust/compiler/src/codegen/llvm/functions/calls.rs` (~lines
236-271) inlines `rt_len` and detects strings ONLY via the hosted runtime's
4-byte "STR1" magic (`kind_u32 == 0x53545231`, `src/runtime/runtime_native.c`).
The freestanding kernel runtime
(`src/os/kernel/arch/riscv64/boot/freestanding_runtime.c`) tags strings with a
single-byte `RtHeapHeader.object_type == RT_HEAP_STRING (0x01)` instead. So on
the freestanding lane every heap string matched neither the string magic nor
the array kind (0x02), and the inline sequence's phi returned the `-1`
("invalid") arm without ever calling `rt_len`/`rt_string_len`. Array `.len()`
worked because both tiers use kind byte `0x02`; `starts_with`/`find`/`split`/
`trim` worked because they are real runtime calls, not inlined.

**Fix:** add an `object_type == 0x01` string check OR-ed with the existing
magic + array checks (safe on the hosted tier: no hosted heap kind has
byte0 == 1 — STRING magic byte0=0x31, ARRAY=0x02, ENUM=0x04, DICT=0x06). Both
layouts store the i64 length at offset 8, so the existing len load is correct
for both. Verified in the emitted RV64 code: the inline site becomes the
optimized range check `addi a2,a2,-1; li a3,0x1; bgeu` (kind byte in {1,2})
instead of `li a3,0x2; beq` (array only).

**Gate:** fresh seed (cargo `--features llvm`) + `rm -rf .simple/native_cache`
+ stamped native-build of `build/os/simpleos_riscv64.elf`, then
`sh scripts/qemu/qemu_rv64_http_test.shs --with-db --expect-http-only
--allow-prebuilt-artifact` → **5/5 PASS (codex-41 in SELECT)**. Note: commit
458524b4915 independently reworked `simple_db_service.spl` to connection-close
framing (avoids `text.len()` on the request path), so the DB gate also passes
without the seed fix on current sources; the seed fix is proven at the
instruction level (above) and un-breaks `text.len()` for all other
freestanding RV64 code.

**WC hazard note:** the seed source edit was clobbered once by a
parallel-session workspace reconcile; recovered from snapshot commit
`9ef0004deea6`. Verify `len_is_string_byte` is present in `calls.rs` before
rebuilding the seed.

## Original report (pre-fix)
**Severity:** high (silent wrong values; corrupts HTTP framing and body slicing in the boot DB service)
**Component:** seed native-build codegen — `--backend llvm --target riscv64-unknown-none --opt-level=aggressive` (freestanding entry-closure lane)
**Found:** 2026-07-11, SimpleOS RV64 DB server gate (`scripts/qemu/qemu_rv64_http_test.shs --with-db`)

## Symptom

In `src/os/services/database/simple_db_service.spl`, on the RV64 LLVM
freestanding path, every `text.len()` call yields nil (renders as `-1` in
string interpolation, behaves as `-1` when passed to `slice`):

- `_simple_db_http_response`: `Content-Length: {body_len}` renders
  `Content-Length: -1` even though `body_len` is a plain hoisted local
  (`val body_len = body.len()`).
- `execute_http_request`: `request.slice(separator + 4, request_len)` with
  hoisted `val request_len = request.len()` still drops the request body's
  last byte (slice end = -1), so `CREATE users` creates table `user` and the
  following `INSERT users ...` returns `ERR table not found`.

IMPORTANT correction to the in-source comments: the original diagnosis
("chained-method bug — only when `.len()` is nested as a call/interpolation
argument") is WRONG or incomplete. Verified 2026-07-11 with a fully fresh
build (`.simple/native_cache` deleted; `Build complete: 51 compiled, 0
cached, 0 failed`): both the hoisted-local and the nested-call variants
misbehave identically at runtime.

Scope observations in the same binary (so not a blanket string-runtime
failure):

- Working on the same `text` values: `starts_with`, `find`, `split`, `trim`,
  string equality, string interpolation of literals, `[text].len()` (array
  len is correct — `parts.len() == 2` dispatches `CREATE`).
- Broken: `text.len()` in every position tried (nested arg, interpolation
  operand, hoisted `val`).
- Freestanding runtime C (`src/os/kernel/arch/riscv64/boot/
  freestanding_runtime.c`) `rt_len`/`rt_string_len` return the correct length
  (or 0 for non-strings, never -1), so the emitted code is not reaching them;
  the call site itself produces the nil encoding.

## Repro

1. Build fresh (no cache): `rm -rf .simple/native_cache && src/compiler_rust/target/release/simple native-build --source build/os/generated --source src --source examples --backend llvm --opt-level=aggressive --log on --entry-closure --entry src/os/kernel/arch/riscv64/boot.spl --target riscv64-unknown-none -o build/os/simpleos_riscv64.elf --linker-script src/os/kernel/arch/riscv64/linker.ld`
   (needs the `rt_invlpg` definition in `freestanding_runtime.c` and the
   `me`-method arity workaround in `simple_db_service.spl`, see
   `stage4_seed_llvmlib_method_arity_2026-07-06.md`).
2. `sh scripts/qemu/qemu_rv64_http_test.shs --with-db --expect-http-only --allow-prebuilt-artifact`
3. Observe the DB step: `Content-Length: -1` on every response and
   `OK CREATE` followed by `ERR table not found` for `INSERT`/`SELECT`.

## Impact

- SimpleOS RV64 DB gate stuck at 4/5 (`codex-41` SELECT evidence unreachable).
- Any freestanding RV64 Simple code that uses `text.len()` computes garbage.

## Service workaround

The boot DB no longer uses `text.len()` for HTTP body slicing or framing. The
boot listener's 1024-byte read cap supplies a clamped slice end, and `Connection:
close` frames responses without a bogus content length. The QEMU checker now
rejects historical `Content-Length: -1` evidence. This mitigates the DB route;
the compiler defect remains open.

## Related

- `doc/08_tracking/bug/native_string_method_returns_neg1_core_c_bootstrap_2026-05-29.md` (older -1-returning string-method class, bootstrap C path)
- `doc/08_tracking/bug/interp_method_call_result_as_arg_corruption_nested_2026-06-30.md` (interp-tier cousin)
- `doc/08_tracking/bug/native_build_noncritical_skip_stale_cache_masking_2026-07-11.md` (why this stayed hidden behind stale cache objects)
