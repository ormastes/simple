# `std.generator` `take()` segfaults under the default JIT execution mode

- Status: OPEN (2026-09-13)
- Area: Rust seed JIT (codegen/execution), out of scope for a pure-Simple bugfix lane
- Severity: P1 — native crash (SIGSEGV / core dump), not just a wrong answer

## How found

While re-verifying `generator_take_returns_empty_after_name_collision_fix_2026-08-17.md`
(closed for the interpreter path by d7213eb6174), the same exact repro was run
under the binary's DEFAULT execution mode (no `SIMPLE_EXECUTION_MODE` override,
i.e. JIT):

```simple
use std.generator.{generate_range, take}

fn main():
    val g = generate_range(0, 3)
    print(take(g, 2))
```

```
$ bin/simple run /tmp/gen_repro.spl
timeout: the monitored command dumped core
```

Under `SIMPLE_EXECUTION_MODE=interpreter` the identical file runs cleanly and
prints `[0, 1]` (exit 0).

## Binary

`bin/simple` -> `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`,
`Simple Language v1.0.0-rc.1` (Rust bootstrap seed), sha256 prefix `3d120a6f`.

## Scope note

This is a JIT/codegen defect in the Rust seed (`src/compiler_rust/**`), not
pure-Simple `src/lib`/`src/app`/`src/compiler` source — the `Iterator<T>` class
with a `fn(T) -> (T, bool)` field and the tuple-destructuring step in
`iter_collect` are exactly the kind of shape (generic class with a function-typed
field, tuple return) that has caused native-codegen corruption elsewhere in this
tree (see `native_class_array_field_mutation_segfault_2026-07-17.md`,
`jit_packed_bitfield_field_read_returns_nil_2026-08-10.md`). Left OPEN; needs a
seed-side JIT investigation, not a stdlib fix.

## Next steps

1. Narrow which of `Iterator<T>`'s fields (the `fn(T) -> (T, bool)` closure
   field specifically) triggers the native codegen fault — bisect by stripping
   fields from a minimal repro class.
2. Check whether the crash is specific to `generate_range`'s closure
   (`fn(n): (n + 1, n + 1 < end_val)`) or general to any generator use under JIT.
