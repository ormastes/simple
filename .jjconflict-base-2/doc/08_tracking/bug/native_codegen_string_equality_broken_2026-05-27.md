# Bug: Native codegen string equality broken

**Date:** 2026-05-27
**Severity:** Critical (blocks bootstrap)
**Status (string-equality bugs):** RESOLVED — Bug A and Bug B verified fixed 2026-05-29.
**Status (871-stub bootstrap blocker):** OPEN — separate issue, not addressed here. See "Deeper blocker" section.
**Component:** Rust seed codegen (native-build)

## Summary

Compiled native binaries produce incorrect results for string `==` comparisons.
The interpreter works correctly. This blocks stage2 bootstrap since the compiled
CLI binary cannot dispatch commands or parse options.

## Two distinct bugs

### Bug A: Local string `==` compares length only

```spl
val a = "human"
val b = "hello"
if a == b:
    print "BUG"   # <-- this branch is taken (both 5 chars)
```

### Bug B: Struct field string `==` always returns TRUE

```spl
val lm = log_opts.log_mode   # value is "human"
if lm == "json":
    print "BUG"   # <-- this branch is taken (different lengths!)
```

## Root cause

The Rust seed codegen generates inline string comparison code that:
- Bug A: compares only the length field, not the content bytes
- Bug B: appears to always evaluate true for struct field access comparisons

The runtime provides correct implementations (`rt_native_eq`, `rt_native_neq`,
`rt_value_eq` in `src/runtime/runtime_equality.c`) that use `memcmp`, but the
codegen never emits calls to them. Instead it generates its own broken inline
comparison.

## Evidence

### Symbol analysis
- `libsimple_runtime.a`: `rt_native_eq` is T (strong, defined)
- Compiled binary: `rt_native_eq` is W (weak stub) -- codegen emits its own weak
  version and never references the real one

### Interpreter confirmation
```
$ bin/release/simple /tmp/test_seed_eq.spl
OK1: human!=hello    # correct
OK2: human==human    # correct
OK3: human!=json     # correct
```

### Compiled binary behavior
```
DEBUG: eq test human==json
OK: human==json is FALSE        # different lengths -- length check passes
BUG: human==hello is TRUE       # same length (5) -- length-only comparison
BUG: lm==json TRUE              # struct field -- always true
```

## Impact on CLI

1. `cli_clean_log_args` strips ALL args: `"--version"` (9) matches `"--verbose"` (9)
2. `log_opts.log_mode == "json"` always true: CLI outputs JSON instead of human text
3. All command dispatch via `match first:` unreliable

## Repro

```bash
bin/simple native-build --entry-closure --clean -o /tmp/simple_debug
echo 'fn main() -> i64:
    val a = "human"
    val b = "hello"
    if a == b:
        print "BUG: same-length different content"
    else:
        print "OK"
    return 0' > /tmp/test_eq.spl
bin/release/simple /tmp/test_eq.spl        # interpreter: OK
/tmp/simple_debug /tmp/test_eq.spl         # compiled: BUG
```

## Deeper blocker: 871 stubbed symbols in stage2 [STILL OPEN — NOT addressed by this fix]

The string equality bug is real but secondary. The compiled stage2 binary has
**871 symbols stubbed as weak functions** by `--entry-closure`, including the
entire `backend__build_native__*` family and `cli_native_build` itself. This
means the stage2 binary can run `--version` but **cannot compile code**.

### Symbol evidence
```
nm /tmp/simple_stage2 | grep -c ' W '   → 871 weak stubs
nm /tmp/simple_stage2 | grep cli_native_build → W (weak, stubbed)
```

### Historical context

The prior "bootstrap" used `bootstrap_emit_seed_wrapper` — a C shim that
`exec()`'d the Rust seed binary. This was deliberately removed in a prior
session. Without it, the stage2 has no compilation capability.

### Architecture options

1. **Restore the seed wrapper shim** — re-enable `bootstrap_emit_seed_wrapper`
   so stage2 delegates compilation to the Rust seed. Fastest path but re-
   introduces the exec() dependency.
2. **Rust codegen fix** — modify the Rust seed's codegen to resolve the 871
   stubbed symbols (emit calls to runtime functions, fix string equality).
   Addresses root cause but requires Rust changes.
3. **Resolve 871 symbols in .spl** — ensure all 871 unresolved modules compile
   and link into stage2 without `--entry-closure` stubbing. Most ambitious;
   currently 27 modules fail to compile without `--entry-closure`.

## Verification (2026-05-29)

Both bugs A and B no longer reproduce against the current working tree.

### Test binary: Bug A (same-length different content)
```
$ /tmp/test_eq_binary
OK1: human!=hello
OK2: human==human
OK3: human!=json
exit: 0
```

### Test binary: Bug B (struct field string ==)
```
$ /tmp/test_struct_binary
OK1: human!=json
OK2: human==human
OK3: struct field human!=json
exit: 0
```

### Symbol check
```
$ nm /tmp/test_eq_binary | grep rt_string_eq
0000000000401644 T rt_string_eq    ← T (strong), not W (weak)
```

### Fix trace
- **Bug A (length-only compare):** Fixed in `src/compiler_rust/compiler/src/codegen/instr/core.rs`
  in commits between 2026-05-15 and 2026-05-28 (git log shows `core.rs` mtime 2026-05-28 11:22).
  `compile_binop` now routes `BinOp::Eq` with STRING type through
  `compile_text_eq_with_identity_fast_path` → `call_runtime_2("rt_string_eq", ...)`.
- **Bug B (struct field == always true):** Fixed by the same change. `build_vreg_types` in
  `body.rs` correctly propagates `TypeId::STRING` from `MirInst::FieldGet { field_type }`,
  so the text fast-path is taken for struct field string comparisons too.
- **Runtime:** `rt_string_eq` added to `src/runtime/runtime_native.c` (mtime 2026-05-28 08:57)
  and registered in `src/compiler_rust/compiler/src/codegen/runtime_sffi.rs` line 345.

### Latent note: duplicate `rt_native_eq` in `runtime_equality.c`
`runtime_equality.c` defines its own `rt_native_eq` (tag-heap approach), conflicting
with the one in `runtime_native.c` (RtCoreString registry approach). However
`runtime_equality.c` is NOT compiled into the core-c-bootstrap runtime archive
(`build_core_c_runtime_library` in `tools.rs` only lists `runtime_native.c`,
`runtime_legacy_core.c`, `runtime_mcp_core.c`, `runtime_simd_utf8.c`). So there is
no ODR conflict in the actual build. Cleanup is a low-priority housekeeping item.

## Latent: .spl textual MIR-to-LLVM backend (2026-05-29)

The .spl `mir_to_llvm_part2_part1.spl` `Eq`/`Ne` cases use `icmp eq`/`icmp ne`
on the raw LLVM value. In the MIR type system, strings are `Ptr(I8, false)` →
LLVM `ptr`, so `icmp eq ptr` compares pointer addresses (identity), not string
content. However, `rt_native_eq` cannot be used here because it operates on
boxed `i64` RuntimeValues, not raw `ptr`. A correct fix for the textual backend
requires either:
1. Lowering string `==` to a `call @rt_string_eq(ptr, ptr)` (needs a ptr-based
   string comparison runtime function), or
2. Ensuring MIR lowering emits explicit string-equality calls before the backend
   sees a pointer `Eq` instruction.

**Production impact:** Verified that `native-build` uses the Rust seed's inkwell
LLVM backend (which correctly calls `rt_native_eq`), NOT this textual path.
Whether the textual `MirToLlvm` path (`driver_bootstrap.spl`) is exercised in
actual bootstrap workflows is unconfirmed. Treat this as a latent correctness
issue in the textual backend — it WILL miscompile `ptr` equality if reached.

## Proposed fix (string equality only — HISTORICAL, no longer needed)

The codegen (in the Rust seed) needs to emit calls to `rt_native_eq` for string
operands instead of generating inline comparison. The function exists in
`src/runtime/runtime_equality.c` and is linked into `libsimple_runtime.a`.

### Verified .spl workaround

`fn str_eq(a, b) -> bool: a.len() == b.len() and a.starts_with(b)` works
correctly in compiled native code (verified via exit codes). However, this
workaround does NOT address the 871-stub blocker — it only fixes string
comparisons if the code reaches them.
