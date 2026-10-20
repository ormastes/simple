# Native build: imported function used as a value calls through NULL; C `rt_array_extend_i64` corrupts packed bytes

- **Date:** 2026-10-20
- **Status:** fixed (HIR value type + cranelift `$boxed` import thunk); linker workarounds removed
- **Found by:** native-building `test/05_perf/compiler/linker/internal_link_spec_driver.spl`
  (seed `b37262fb`, cranelift, `SIMPLE_NATIVE_BUILD_RUST=1`, core-c-bootstrap runtime)

## 1. Imported function as a value: NULL call (fixed)

`elf_operation_bindings.spl` stored `Some(file_read_bytes_result)` and `Some(elf_exec_plan)`.
Both functions are defined in another unit. Calling the stored `fn` value jumped to
address 0.

Backtrace, frame #1:
`compiler__backend__linker__elf__elf_operation_bindings__ElfSealedOperationsV1_dot_read_bytes`

Functions defined in the same unit (`_elf_builtin_relocate`, `_elf_builtin_write`) get a
`$boxed` thunk in `nm`. The imported ones get none.

Root cause, two layers:

1. **HIR.** `import_loader.rs` registers an imported function in `globals` under its
   RETURN type. `named_callable_value_type` only answered a `HirType::Function` for
   functions defined in the unit, so `add_one` as a value was typed `i64`
   (`GlobalLoad ... ty: TypeId(5)`). MIR then `BoxInt`ed the code pointer before
   `OptionSome`, which is what crashed the LLVM build (`ldp [x19]` after
   `rt_enum_payload`).
2. **Cranelift.** `emit_boxed_fn_value_entries` only thunked functions with a body in
   the unit. An imported name fell to a bare `rt_alloc` "direct record" that
   `rt_closure_func_ptr` rejects, so `compile_indirect_call` called address 0.

Fix: the import loader records each imported free function's `HirType::Function` in a
side map (`imported_function_value_types`; `globals` still holds the return type) and
`named_callable_value_type` answers it. Cranelift emits a local `F$boxed` thunk for
every bodiless function loaded as a function-typed value; it calls the import through
`func_addr` (one relocation to the symbol) with the uniform all-`i64` user-function
signature, so a placeholder `(i64) -> i64` import declaration cannot mismatch. The two
direct-record fallbacks in the cranelift `GlobalLoad` now fail the function's
compilation instead of building a NULL function value; a missing symbol is a link error.

Test: `src/compiler_rust/compiler/tests/imported_fn_value_native.rs` native-builds
`test/fixtures/native/imported_fn_value` (variable, struct field, callback, typed
`Option<fn>` local and struct field, `text` function) with cranelift and llvm. Before:
cranelift SIGSEGV at pc 0, llvm SIGSEGV in `spl_main`. After: both print
`imported-fn-value PASS`.

The local thunks `_elf_builtin_read_bytes` and `_elf_builtin_layout` are removed;
`elf_operation_bindings.spl` stores `file_read_bytes_result` and `elf_exec_plan`
directly again.

Found while testing (not import-specific); fixed in section 3.

## 3. Follow-ups: untyped `Some(f)`, module-level fn values, pool (fixed)

Fixtures: `test/fixtures/native/fn_value_followups/` (`option_untyped.spl`,
`global_fn.spl`, `pool_fn.spl`), run on both backends by
`src/compiler_rust/compiler/tests/fn_value_followups_native.rs`.

1. **LLVM, untyped `val m = Some(f)`.** HIR typed every `Some(x)` as ANY, so
   `case Some(h)` bound `h` as ANY and the indirect call through it mixed the raw and
   tagged conventions: a wrong result, even for a LOCAL `f`. An annotated
   `Option<fn(..)>` worked. Fix (`hir/lower/expr/calls.rs`): `Some(x)` with a
   function-typed payload answers `Option<fn(..)>`, the same type the annotation gives.
   Other payloads keep ANY.
2. **Cranelift, module-level `val G: fn(..) = F`.** `generate_module_init` stored the
   raw direct record, which `rt_closure_func_ptr` rejects, so a call through `G` went to
   address 0. Fix: `emit_boxed_fn_value_entries` also emits `F$boxed` for every
   function named by a global initializer (a local body, or an import whose arity
   comes from the global's own function type), and the initializer stores
   `rt_closure_new(F$boxed, 0)`, the same value a `GlobalLoad` builds. Only an extern
   entry point keeps the direct record. A user function with no thunk fails the
   build instead of storing a value that calls address 0.
   The UNTYPED `val G = f` was worse on both backends: the module pass typed `G` as
   ANY, so it was never recorded as a function initializer, and `G(5)` lowered as a
   direct call to a function named `G` (build error: "cross-module call 'LOCAL_FN'
   resolved to data/type export"). Fix (`module_pass.rs`): each declared free function
   records its `HirType::Function` (`declared_function_value_types`), and `val G = f`
   naming a declared or imported function takes that type. LLVM's module initializer
   also declares an import named only by such an initializer (all-`i64` signature,
   arity from the global's type) instead of failing with "unknown function".
3. **Pool.** `rt_pool_state_try_submit_i64_v1` accepted only the direct record, so
   cranelift function values (closures) were refused with -3. Fix (adapt at the
   boundary, `runtime_thread.c` and its twin `runtime_pool.c`): the direct record is
   tested first; otherwise `rt_closure_func_ptr` must answer a registered closure, and
   the task calls its boxed entry with `rt_value_int(input)` and decodes the result
   with `rt_value_unbox_int`. Any other value is still refused at submit.

Evidence (seed `--profile bootstrap --features llvm`): before, 4 of 6 failed:
`option_untyped_fn_value_llvm` (exit 1), `pool_fn_value_cranelift` (exit 2, submit
refused), and `global_fn_value_{cranelift,llvm}` (build error above; the typed
`val G: fn(..) = f` form SIGSEGVs under the seed JIT). After: 6/6, and
`imported_fn_value_native`, `fn_ref_value_jit` and `optional_array_coalesce_native`
still pass.

Still open (Opus review):
- The pool does not retain a submitted closure. A capturing lambda created inside a
  transient scope and joined after that scope ends is a use-after-free. Zero-capture
  function values are safe because their thunk never reads the closure.
- The Rust-runtime pool twin (`runtime_pool.c` in `simple-runtime`) has no native
  test. The fixtures link only `core-c-bootstrap`.
- `declared_function_value_types` resolves parameter types during the declaration
  pass, so a parameter whose struct is declared later becomes ANY. Cranelift is
  unaffected (its thunk uses the compiled function). LLVM takes argument handling
  from the value type.

## 2. C runtime `rt_array_extend_i64` on `[u8]` and `[u64]` (fixed)

`src/runtime/runtime_native.c` copied element by element as
`rt_array_push(d, rt_array_get(s, i))`. For a byte array, `rt_array_get` returns the raw
byte, but `rt_array_push` decodes its argument as a tagged value. Every byte that is a
multiple of 8 was therefore divided by 8. A CIE length of 0x10 became 0x02 in a linked
`.eh_frame`, and 0x78 became 0x0f.

Fix: packed byte arrays now copy raw bytes with `memmove`, matching the Rust runtime
(`collections.rs rt_array_extend_i64`). A packed/unpacked mix is refused, as Rust does.
The source is re-read after reserve, so self-extend is safe.

Follow-up (U64_PACKED): the generic loop also moved a slot word verbatim when exactly
one side was a `[u64]` (raw words) and the other a generic array (tagged words): raw 9
read back as a non-int, tagged 5 as 40. `[u64]` to `[u64]` now copies whole host-order
`int64_t` words with `memmove` (same layout on both sides, so byte order never changes
meaning); a mixed pair re-encodes each element through `spl_core_slot_value` /
`spl_core_store_element`. Pinned by `src/runtime/test/rt_array_extend_packed_selfcheck.c`
(red before at the `[u64]` -> generic check, 38 checks green after).

## Verification

The native driver's output is byte-identical to the interpreted driver
(`cmp`) for `hello_libc_a64.o` (exit 42) and `wide_str_a64.o` (exit 44).

| driver | link time |
|---|---|
| native | 13-20 ms |
| interpreted | 760 ms |
