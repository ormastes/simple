# `"7".to_i64()` returns a `.rodata` pointer under native codegen (2026-09-07)

**Status:** OPEN. Pre-existing; NOT introduced by, and NOT cured by, the
`rt_to_int_dynamic` routing fix landed the same day.

## Measured

Built with a patched seed (`--backend llvm --mode one-binary --entry`) and run:

```
A to_i64('1') ?? 0            => 2100660     # raw literal   WRONG
B to_i64('1650000') ?? 0      => 2100696     # raw literal   WRONG
C to_i64('notanumber') ?? 0   => 2100628     # raw literal   WRONG
D to_i64(concat '4') ?? 0     => 4           # heap string   CORRECT
```

The three wrong values are consecutive `.rodata` addresses — the literals' own
pointers. Interpreted under the seed the same file prints `1`, `1650000`, `0`,
`4`, so the interpreter is the oracle and native codegen disagrees with it.

## Why

`.to_i64()` on an erased receiver lowers to `rt_to_int_dynamic`, which is
deliberately receiver-dispatched:

* C  (`src/runtime/runtime_native.c:5488`): `rt_core_as_string(v)` -> parse,
  else IDENTITY.
* Rust (`src/compiler_rust/runtime/src/value/collections.rs`):
  `heap_type() == String` -> parse, else IDENTITY.

A `text` LITERAL is not a heap string in either runtime: it is a bare pointer
into `.rodata`, which neither predicate recognises, so both fall to the identity
arm and hand the pointer back. A heap string (concatenation, interpolation,
`rt_string_new` — including every element of `rt_get_args`, `value/args.rs:248`)
is recognised and parses correctly, which is why the `--threads` bootstrap
blocker is fixed while this is not.

## Why the obvious fix is wrong

`rt_string_len` and `rt_string_data` handle raw literals with a
`value >= 0x10000` pointer heuristic. That is safe for them because their
argument is always a `text`. It is NOT safe here: `rt_to_int_dynamic`'s whole
purpose is to be the identity for an erased receiver that may be a genuine
number, and any `i64 >= 65536` would then be dereferenced as a pointer.
`rt_to_int_dynamic`'s own C comment records this reasoning and rejects a bare
tag test for the same reason.

## Likely shape of a real fix

Type-directed rather than value-directed: where the front end still knows the
receiver is `text`, emit `rt_string_to_int_any` (which normalises through
`rt_interp_cstr` and is already correct for both tagged and raw buffers)
instead of leaving the receiver erased. That keeps the erased-receiver identity
contract intact for genuine numbers.

## Scope

Affects any native `text_literal.to_i64()` / `.to_int()`. Not reached by the
interpreter, and not reached when the text came from argv, a file read, a
concatenation, or an interpolation.
