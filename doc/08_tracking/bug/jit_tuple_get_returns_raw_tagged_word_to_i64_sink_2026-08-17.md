# JIT: `tuple.get(i)` hands a RAW TAGGED word to an `i64` sink — `5` reads back as `40`

**ID:** jit_tuple_get_returns_raw_tagged_word_to_i64_sink_2026-08-17
**Date:** 2026-08-17
**Severity:** P1 — silent wrong value, exit 0, no diagnostic.
**Status:** OPEN — reproduced and minimised, not fixed.

## How it was found

Not by looking for it. It was caught by the *similar-problem detection* probe
written for
`doc/08_tracking/bug/i8_array_literal_reads_back_wrong_value_2026-08-17.md`
(`test/01_unit/compiler/codegen/probe_int_width_boxing_matrix_jit.spl`), whose
`tuple_i64_0` row failed while the i8 reproducer it was generalising from said
nothing about tuples. That is the seventh time today a prevention spec caught a
defect its own reproducer missed.

## Reproduction (measured 2026-08-17, `bin/simple` = Rust seed)

```simple
fn takes(x: i64) -> i64:
    x

fn main():
    val t = (5, 6)
    val a: i64 = t.get(0)
    print a                 # JIT: 40    interpreter: 5
    print takes(t.get(0))   # JIT: 40    interpreter: 5
    print t.get(0) + 0      # JIT: 5     interpreter: 5   <- correct
    val l = [5, 6]
    print takes(l.get(0))   # JIT: 5     interpreter: 5   <- arrays are fine
```

```
$ SIMPLE_EXECUTION_MODE=jit bin/simple run tup3.spl
40
40
5
5
5
$ SIMPLE_EXECUTION_MODE=interpreter bin/simple run tup3.spl
5
5
5
5
5
```

`40 == 5 << 3`, i.e. the runtime TAG_INT word for 5 (`v << 3 | 0b000`) delivered
un-untagged. `print t.get(0)` on its own is CORRECT — the print path accepts a
tagged RuntimeValue — so the defect only shows when the erased `.get()` result
flows into a slot or parameter statically typed `i64`, which is exactly where no
unbox is emitted.

## Why this matters / relation to other rows

This is the same family as
`doc/08_tracking/bug/jit_corrupts_i64_array_returned_from_sha1_bytes_2026-08-04.md`
("a raw tagged word read as if it were already untagged"), but on the tuple
`.get()` path rather than the array one. Arrays are clean here; tuples are not.

Scale factor: `x8`. Any code that reads an i64 out of a tuple into a typed
binding gets a value eight times too large, silently. `.get()` on a tuple is the
idiomatic way this tree returns multi-value results (e.g. the whole
`(list, list, i64, i64)` streaming-hash context shape in
`src/lib/common/crypto/sha1.spl`).

## Not yet done

- Which lowering site omits the unbox (array `.get()` emits one, tuple `.get()`
  does not — the asymmetry is the lead).
- Whether `u64`/`i32` tuple sinks are affected: `tuple_u64_0` and `tuple_i32_0`
  PASS in the matrix probe, so this may be i64-specific, which would point at a
  "same machine width, therefore no conversion needed" shortcut.
- Whether struct fields and dict values share it.

## Detection

`test/01_unit/compiler/codegen/probe_int_width_boxing_matrix_jit.spl`, row
`tuple_i64_0`, asserted by
`test/01_unit/compiler/codegen/int_width_boxing_matrix_class_spec.spl`. That
spec is expected to be RED on this row until this bug is fixed; per
`.claude/rules/testing.md` the assertion is left in place rather than weakened.
