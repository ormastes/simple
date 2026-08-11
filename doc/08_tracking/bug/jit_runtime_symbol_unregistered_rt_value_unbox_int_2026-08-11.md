# JIT emits calls to runtime symbols that were never registered (`rt_value_unbox_int` family)

Status: FIXED 2026-08-11
Severity: BLOCKER (origin/main tip produced a JIT-broken compiler)

## Symptom

A pristine build of `origin/main` at `b6d717e62e2` failed at run time with:

```
unresolved external symbol 'rt_value_unbox_int'
```

The JIT lane then silently fell back to the interpreter.
`scripts/check/check-numeric-builtin-result-type.shs` reported 23 wrong
(empty strings) and `check-native-unwrap-enum-receiver.shs` failed.

The DEPLOYED binary (built 04:14 the same day) passed everything — the
registration existed only inside that binary's build, never in source. This
is the *stranded-in-binary / missing-in-source* shape: a working artifact is
not evidence that the source can reproduce it.

## Root cause — the registration mechanism IS the list

`src/compiler_rust/runtime/build.rs:52` parses
`pub const RUNTIME_SYMBOL_NAMES` out of
`src/compiler_rust/common/src/runtime_symbols.rs:381` and generates
`RUNTIME_SYMBOL_ENTRIES` (build.rs:102-116), the table
`register_static_runtime_symbols()` (`runtime/src/lib.rs:316`) publishes and
`StaticSymbolProvider::get_symbol` (`native_loader/src/static_provider.rs:26`)
answers from. `codegen/jit.rs:391` registers a JIT symbol only when that
provider (or the ELF fallback) resolves the name.

So a symbol absent from `RUNTIME_SYMBOL_NAMES` is **never registered**, no
matter that it is defined in the runtime and declared in
`codegen/runtime_sffi.rs`.

`rt_value_unbox_int` was:
- emitted: `codegen/instr/mod.rs:1495`, `codegen/cranelift_emitter.rs:788`
- spec'd:  `codegen/runtime_sffi.rs:555`
- defined: `runtime/src/value/sffi/value_ops.rs:80`, `src/runtime/runtime_native.c:2179`
- **absent** from `common/src/runtime_symbols.rs` `RUNTIME_SYMBOL_NAMES`

Nothing in the build fails when an emitted symbol is unlisted — the gap is
only observable at run time.

## Family audit (do not fix one and leave brothers)

Diffed every name codegen emits (`call_runtime_*`, `runtime_funcs.get`,
`declare_function`, `get_function`) against `RUNTIME_SYMBOL_NAMES`: 109
emitted, 15 unlisted. Of those 15, three are actually defined in a runtime and
were therefore genuinely broken; the rest have no definition anywhere
(`rt_await`, `rt_contract_check`, `rt_unit_bound_check`, `rt_generator_yield`,
`rt_future_*`, `rt_par_for_each`) or are monoio symbols reached by another
path.

Fixed (added to the list):
- `rt_value_unbox_int`     — Rust + C runtime; the reported failure
- `rt_struct_receiver_valid` — C runtime; added by today's `a1bcda91f6`, same gap
- `rt_dict_insert`         — C runtime; pre-existing, same shape

Verified clean by family: `rt_math_*` (33/33 listed), `rt_unwrap_*` (2/2,
`rt_unwrap_or_trap` landed correctly), `rt_value_*` (14/14 after this fix).

## Fix

`src/compiler_rust/common/src/runtime_symbols.rs` — three names added to
`RUNTIME_SYMBOL_NAMES` with a comment stating that listing here *is* the
registration and that codegen must not emit a call to an unlisted symbol.

## Verification (candidate `/mnt/data/cargo-target-clean/release/simple`)

```
PASS — 9 probe(s) checked                                   # check-deployed-binary-capabilities
PASS — 48 assertions checked across 2 lanes, 0 failures     # check-numeric-builtin-result-type
PASS — 4 checked                                            # check-native-unwrap-enum-receiver
```

## Follow-up (not done here)

There is no gate that fails when codegen emits a runtime symbol missing from
`RUNTIME_SYMBOL_NAMES`. That check is mechanical (the diff above is ~20 lines
of script) and would have caught this at build time rather than at run time.
