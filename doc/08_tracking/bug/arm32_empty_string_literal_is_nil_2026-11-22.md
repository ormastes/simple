# arm32 freestanding: every empty string literal lowers to nil

Status: open (reported by lane arm32-text-shims, 2026-11-22)

`examples/09_embedded/simple_os/arch/arm32/boot/baremetal_stubs.c:353`
`rt_string_new` returns `NIL_VALUE` for `len <= 0`, and `rt_string_new_literal`
(line 348) forwards to it. So on arm32 every `""` literal is nil, while the
pure-Simple text shims (`src/os/kernel/arch/arm32/runtime_text_shims.spl`)
build real zero-length heap strings (builder finish, slice, from_byte_array).
`built_empty == ""` is therefore false on arm32 (`rt_text_eq_any` compares
nil only with nil, matching hosted dict-miss semantics).

Fix: make `rt_string_new` allocate a zero-length string (`len == 0`), keeping
nil only for `len < 0` / OOM; add a repro spec comparing a sliced empty string
with `""`.

Also: codegen emits `__simple_rt_string_byte_at` / `__simple_rt_string_char_code_at`
(50.mir method_calls_literals.spl:5695,5760). HIR reserves those names for the
core-string module (declaration_lowering.spl:210-217), so they cannot be
defined from the arm32 shim file; if the arm32 link reports them undefined,
they must be provided by the core-string alias owner.
