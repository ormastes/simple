# Raw string-find interpreter registration

## Observed release blocker

The fully hydrated release push gate at local commit
`f385a8bc1657c075726e4adf322b9b175da069b1` rejected 238 compiler externs with
one new gap, `rt_string_find`, and one stale baseline entry,
`rt_string_index_of`. Evidence:
`D:/dev/simple-astra-nul-concat-release-20260930/build/native_probe/runtime-concat-nul/push-release-complete-inputs.log`.
Main `0814a6dfa5e` has the same missing registration.

`src/compiler/10.frontend/core/types.spl` declares and calls `rt_string_find`
after the raw-byte-offset correction. The old Rust runtime
`rt_string_index_of` returns a boxed Option and is not interchangeable with
this primitive. The C owner `src/runtime/runtime_native.c` defines find as
the first byte offset, `-1` for no match, and `0` for an empty needle.

## Source correction

The string interpreter owner now implements `rt_string_find_fn` and registers
it in the actual `EXTERN_DISPATCH` table. It returns `Value::Int`, including
`-1` on a miss, rather than nil or an Option. Both interpreter text values and
existing runtime string handles are accepted. Runtime spans are copied as
bytes before resolving the other argument, preserving embedded NUL and
non-UTF-8 bytes without lossy conversion or borrowed-pointer reuse. Wrong
arity and invalid argument types return errors through existing diagnostics.

Only after adding genuine ownership is the stale `rt_string_index_of`
baseline entry removed. No new gap is baselined, no symbol is renamed to
evade the gate, and the registry checker is unchanged.

## Reproduction and prevention tests

Three tests call the real registered handler in `interpreter_extern/mod.rs`:

- `rt_string_find_is_registered_and_returns_raw_byte_offsets`: registration,
  first occurrence, tail hit, miss, longer needle, both empty cases, UTF-8
  byte offsets, and embedded NUL matching.
- `rt_string_find_preserves_runtime_handle_bytes_and_mixed_arguments`:
  runtime-owned bytes, mixed interpreter/runtime arguments, invalid UTF-8
  before a match, raw-byte needles, and empty needles.
- `rt_string_find_rejects_wrong_arity_and_non_text_arguments`: zero, one,
  and three arguments; nil receiver/needle; non-string integer.

These are authored tests, not execution evidence. The actual baseline gate
failure above is retained. The historical raw-find diagnostic lane exhausted
three verification cycles; root requested source-only preparation. No Cargo
test, registry gate, interpreter/native probe, or bootstrap was rerun here.
Runtime PASS and gate PASS remain pending explicit authorization for a new
verification cycle. Native-build delegation cannot qualify these tests.

## SOSIX host-access audit

The handler performs in-memory byte copying and searching only. Runtime
handle extraction uses the existing `simple_runtime::value` string owner
accessors already used by neighboring string handlers. There are no new
filesystem, environment, process, clock, network, or other host operations,
so no SOSIX host-access adapter is needed. Tests use runtime-owned memory
allocation and release only; they add no direct host I/O.

The patch is isolated from the NUL-concat and hook-path commits, frozen
bootstrap sources, and their caches. Main and release source preparation
does not qualify or publish a release.
