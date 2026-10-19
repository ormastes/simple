# Tracked-seed cranelift build: split secure_temp_dir refuses every snapshot staging (2026-10-19)

- **Status:** fixed (this change). DB reconciliation pending (`bug_db.sdn` row not yet written).
- **Workaround tag:** `bug=tracked_seed_cranelift_split_secure_temp_dir_refuses_20261019`
  (producer3 worktree `C:/dev/simple-producer3-20261019`, `src/lib/nogc_sync_mut/io/file_ops.spl`:
  `secure_temp_dir_raw` restored to the two-argument `rt_secure_temp_dir(host_path_native(parent), prefix)`).
  Remove the workaround once a producer is built from source carrying this fix.

## Failure

producer3 (built from `origin/release_phase3` `35e226ca84a` by
`tracked-seed-3d9d/simple.exe native-build --backend cranelift --target x86_64-pc-windows-msvc`,
exe `C:/dev/simple-bootstrap-storage/producer3-20261019/strict/simple-producer3-strict.exe`)
fails SCV snapshot staging with `SCV-E-ADMISSION: snapshot-staging-create-failed`
(`src/lib/scv/compile_snapshot.spl:518`). No `rt_secure_temp_dir:` diagnostic
is printed, so the failure is before `CreateDirectory`.

## Root cause

The split API (`669c50c11be`, `4fafccac766`) gave
`rt_secure_temp_dir_set_parent` / `_set_prefix` a raw `(ptr, len)` C ABI
(`src/runtime/runtime_native.c:15614,15622` before this fix). That ABI exists
only if the COMPILER has a `text_arg_indices` row for the name
(`src/compiler_rust/compiler/src/codegen/instr/calls.rs:2912`,
`runtime_sffi.rs:2234`, `src/compiler/50.mir/text_extern_abi.spl:93`), and the
rows were added in the same commits. The seed that built producer3
(`tracked-seed-3d9d`, 2026-10-18) predates them: its binary does not even
contain the string `rt_secure_temp_dir_set_parent`. For an extern it does not
know, the seed's cranelift path passes the boxed text handle as one word.

Disassembly of the linked facade
`lib__nogc_sync_mut__sosix__secure_temp_dir__sosix_secure_temp_dir_set_parent`
(0x141b902e4, `mod_1320.o`):

```
movq 0x2eede5(%rip), %rdx   ; rdx = &rt_secure_temp_dir_set_parent
callq *%rdx                 ; rcx = boxed handle, rdx = the callee address
```

So C received `ptr = handle`, `len = <code address>`; `rt_text_arg_to_path`
rejected `len >= RT_TEXT_PATH_MAX`, `set_parent` returned 0, and
`secure_temp_dir_raw` returned `""` without ever reaching `CreateDirectory`.
The link map shows the real definitions bound (`simple_runtime:runtime_native.obj`),
so this is not a stub/twin-parity gap; it is a seed-vintage-dependent ABI.
The two-argument `rt_secure_temp_dir` works because the old seed already had
its `[0, 1]` row.

## Fix

The setters now take ONE boxed text RuntimeValue
(`int64_t rt_secure_temp_dir_set_parent(int64_t)`), decoded in C with
`rt_string_data` / `rt_string_len` (which also accept a literal's raw pointer).
The `(ptr, len)` rows were removed from the Rust seed table and the pure-Simple
MIR twin, and `RuntimeFuncSpec` is `[I64] -> [I64]`. The single-word handle is
the generic crossing every seed and both pure-Simple backends emit, so the
split API no longer depends on any table row. `rt_secure_temp_dir_make` is
unchanged (no arguments).

Caveat: a seed built from `669c50c11be` up to (not including) this fix still
has the old rows and would expand to `(data_ptr, len)`; the C side then sees
`data_ptr` as a non-tagged value and falls back to strlen on it. Rebuild such a
seed rather than relying on that fallback.

## Tests

- `src/runtime/test/rt_secure_temp_dir_split_handle_abi_selfcheck.c` — links
  `runtime_native.c`, checks handle-ABI set/make, nil and `a/b` refusals, and
  slot consumption. Measured PASS on Windows (clang 23, MSVC target).
- `test/01_unit/compiler/mir/secure_temp_dir_split_text_extern_spec.spl` —
  no `(ptr, len)` row for the three split names.
- Rust: `secure_temp_dir_split_setters_take_one_boxed_text_value` in
  `codegen/instr/calls.rs`.
- `clang -fsyntax-only` of `runtime_native.c` clean.
