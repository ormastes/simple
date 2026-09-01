# ByteBuffer struct-parameter mutation lost across a foreign method call (test), segfaults under `run`

Date: 2026-09-01
Status: OPEN
Severity: High — silent data corruption under `bin/simple test` (fail-closed zeros
read back as valid data), SIGSEGV under `bin/simple run`

## Evidence

Discovered while triaging `test/01_unit/lib/common/` unit-test failures.

Reproduces on both:
- `test/01_unit/lib/common/bytes/ints_spec.spl` — "U16le stores 0xBEEF as [0xEF,0xBE]"
  and "U16be stores 0xBEEF as [0xBE,0xEF]"
- `test/01_unit/lib/common/bytes/bytes_foundation_spec.spl` — "U32be + U32le
  serialized into a buffer CRC matches a recomputed CRC"

Command (isolated, single file):

```bash
bin/simple test test/01_unit/lib/common/bytes/ints_spec.spl
```

Observed:

```
Little-endian views
  [PASS] U16le decodes [0x34,0x12] = 0x1234
  [PASS] U32le decodes [0x78,0x56,0x34,0x12] = 0x12345678
  [FAIL] U16le stores 0xBEEF as [0xEF,0xBE]
    expected 0 to equal 190
  [PASS] U32le round-trips 0xDEADBEEF
  ...
Results: 6 total, 5 passed, 1 failed
```

Failing pattern (`ints_spec.spl:15-20`):

```simple
it "U16le stores 0xBEEF as [0xEF,0xBE]":
    var b = ByteBuffer.new()
    U16le.of(0xBEEF).store(b)      # store(buf: ByteBuffer) is a `me` method on
                                     # U16le, taking `b` as a plain parameter and
                                     # mutating it via buf.push_byte(...) inside
    val s = b.freeze()
    expect(s.get(0).to_i64()).to_equal(0xEF)   # actual: 0 (fail-closed empty span)
    expect(s.get(1).to_i64()).to_equal(0xBE)
```

`ByteBuffer.push_byte`/`push_u8` (`src/lib/common/bytes/span.spl:149-154`) push
onto `self.buf`; `U16le.store`/`U32be.store` (`src/lib/common/bytes/ints.spl:146-150`
and sibling) call `buf.push_byte(...)` on the **parameter** `buf`, not on `self`.
After `store()` returns, the CALLER's `b` reads back empty (`freeze()` produces a
0-length span, so `.get(i)` fail-closed-returns `0u8` per `ByteSpan.get`'s
documented bounds-check default) — the mutations performed inside `store()` never
propagate to the caller's variable.

`Crc32.update(span: ByteSpan)` (`src/lib/common/bytes/checksum.spl:31-43`) shows
the same failure shape on `bytes_foundation_spec.spl`'s cross-module CRC test —
`c1.update(span)` (span built via `buf.freeze()` two calls earlier and read
correctly by `span.get()`/`span.len()` in the SAME scope) leaves `c1.raw()==0`
(the untouched initial-state value), while `c2.update(ByteSpan.new(span.to_bytes()))`
computes the correct CRC (154 in the minimal repro below). This is the same
class as the `store()` case but through a different struct/method pair, so the
defect is not specific to `ByteBuffer.push_byte` — it is parameter-mutation loss
in general when a struct value is passed as a **non-self** argument to another
struct's method and mutated by callee-internal `me` calls.

## Minimal repro — segfaults under `bin/simple run` (not just wrong under `test`)

```simple
use lib.common.bytes.span.{ByteSpan, ByteBuffer}
use lib.common.bytes.ints.{U16le}

fn main():
    var b = ByteBuffer.new()
    U16le.of(0xBEEF).store(b)
    val s = b.freeze()
    print "s.len()=" + s.len().to_text()
```

```bash
bin/simple run repro.spl
# exit code 139 (SIGSEGV), no output beyond the seed-binary warning banner
```

A second repro combining `store()` + `Crc32.update()` in the exact shape of
`bytes_foundation_spec.spl` also exits 139 under `run`. `bin/simple test` does
NOT crash — it silently reads back zeros through `ByteSpan.get`'s fail-closed
bounds check, which is why the test failures read as ordinary value mismatches
("expected 0 to equal N") rather than crashes. Per `.claude/rules/testing.md`,
`run` and `test` use different engines (JIT-with-interpreter-fallback vs.
hard-interpreter); this bug is visible on both but manifests differently
(SIGSEGV vs. silent zero-read), which is itself worth noting as a second,
correctness-relevant divergence between the two engines.

## Impact

Any code that passes a mutable struct (here `ByteBuffer`) as a plain argument
into another type's method, expecting the callee's `me`-mutations to be visible
to the caller afterward, silently loses those writes under `test` and can
segfault under `run`. This is a common pattern in `src/lib/common/bytes/ints.spl`
(`U16le`/`U32le`/`U32be`/`U64be`/`U64le` all define `store(buf: ByteBuffer)` this
way) and in `checksum.spl` (`Crc32.update`, `Adler32.update`). The self-contained
`to_span()` helpers (`U32be.to_span()` etc., which create+mutate+freeze their OWN
local `ByteBuffer` inside one function) are unaffected, which is why most specs
in these files pass — only the cross-call chaining pattern breaks.

## RESOLVED (interpreter/`test` lane) 2026-09-01

Root-caused and fixed. Two independent defects, addressed separately:

**1. `ByteBuffer` was a `struct` (value type).** Struct arguments are
deep-copied on parameter pass — this is DOCUMENTED, INTENDED interpreter
behavior (`doc/07_guide/language/value_semantics_by_engine.md`), not a bug.
`ByteBuffer` is a growable accumulator meant to be mutated across
method/function boundaries (`U16le.store(buf)`, `Crc32.update(span)`,
`inflate_fixed_copy_match(out, ...)`), so it was fighting the language's
value semantics. Fixed by changing `struct ByteBuffer:` to `class ByteBuffer:`
in `src/lib/common/bytes/span.spl` (reference type — see the docstring added
there). This alone fixed the DECOMPOSED shape
(`val u = U16le.of(x); u.store(b)`) but not yet the exact spec pattern.

**2. Real interpreter defect: a two-level chained `MethodCall` receiver
dropped write-back of the OUTER call's own mutable arguments.** Minimal
repro: `Wrapper.of(65).store(b)` (chained) lost the mutation to `b`;
`val u = Wrapper.of(65); u.store(b)` (decomposed) did not.
`handle_method_call_with_self_update_inner`
(`src/compiler_rust/compiler/src/interpreter_helpers/patterns.rs`, the
statement-level dispatcher used for a bare expression-statement, a `val x =
...` initializer, or a loop body) has a hand-written branch for exactly this
shape (`if let Expr::MethodCall { .. } = receiver.as_ref()`), added to handle
chains like `self.advance().unwrap()`. It evaluated the outer call's
arguments into bare `Value`s against a **cloned** `env` and dispatched via
`call_method_on_value(inner_result, method, &eval_args, &mut working_env,
...)` — losing both the original `Argument` AST (needed to map an evaluated
value back to a caller identifier) and writing to a clone the caller never
sees again. `write_back_mutable_arguments` / `exec_function_with_self_return`
(the mechanisms that make `x.method(buf)` persist a mutation to `buf`) were
never reached for this shape, confirmed by instrumented tracing (`git log`
this file for the `SIMPLE_DEBUG_WBMA`-gated diagnostics left in
`interpreter_call/core/function_exec.rs` and `interpreter_method/mod.rs`,
useful for any future write-back investigation).

Fix (patterns.rs, in the `Expr::MethodCall` branch of
`handle_method_call_with_self_update_inner`): when `inner_result` is a
`Value::Object` whose class defines `method`, evaluate the outer call's
arguments against the REAL `env` and dispatch through
`find_and_exec_method_with_self_owned_values` (already used elsewhere in this
file for the analogous `self.field.method(...)` shape), which writes any
mutated `Array`/`Dict`/`Object`/`Tuple` identifier argument back into `env`
exactly like the ordinary `x.method(buf)` path. The old
clone-env-then-`call_method_on_value` path is kept as a fallback for
non-Object receivers (a chain ending in a string/array/dict builtin method).

**Verified (interpreter lane, `bin/simple test` — same binary class the repo
tooling uses):**
```
test/01_unit/lib/common/bytes/ints_spec.spl:            11 total, 11 passed, 0 failed   (was 9/11)
test/01_unit/lib/common/bytes/bytes_foundation_spec.spl:  6 total,  6 passed, 0 failed   (was failing)
test/01_unit/lib/common/bytes/span_spec.spl:             11 total, 11 passed, 0 failed
test/01_unit/lib/common/compress/typed/deflate_typed_spec.spl: 37 total, 37 passed, 0 failed
test/01_unit/lib/common/crypto/typed/ctypes_spec.spl:    31 total, 31 passed, 0 failed
test/01_unit/compiler/backend/macho_writer_spec.spl:     39 total, 39 passed, 0 failed
test/01_unit/compiler/backend/native_backend_spec.spl:    4 total,  4 passed, 0 failed
```
All other `ByteBuffer` consumers checked and unaffected/passing.

**NOT fixed — separate, still-open defect: `bin/simple run` (JIT-with-
interpreter-fallback lane) still SIGSEGVs** on the exact repro in this file's
"Minimal repro" section, unchanged by either fix above (re-verified after the
patterns.rs fix, exit 139). This is a JIT-lane crash, not the interpreter
write-back defect fixed here — `test` and `run` are different engines per
`.claude/rules/testing.md`, and this file's own earlier text already noted
the SIGSEGV/silent-zero divergence between them. Left open; not investigated
further in this pass.

## Files changed
- `src/lib/common/bytes/span.spl` — `struct ByteBuffer` -> `class ByteBuffer`.
- `src/compiler_rust/compiler/src/interpreter_helpers/patterns.rs` — write-back
  fix for chained `MethodCall` receivers, described above.
- `src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs`,
  `src/compiler_rust/compiler/src/interpreter_method/mod.rs` — `SIMPLE_DEBUG_WBMA`-gated
  diagnostic tracing added during root-causing; left in (off by default),
  matching the existing `SIMPLE_DEBUG_ARG_BINDING`/`SIMPLE_INTERP_OOB_DEBUG`
  pattern already used elsewhere in this codebase.

## Not fixed here
`bin/simple run` JIT-lane SIGSEGV (see above) — separate defect, still open.
