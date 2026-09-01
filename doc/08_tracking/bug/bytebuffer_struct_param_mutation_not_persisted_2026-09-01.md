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

## Re-verification 2026-09-01 (independent, Windows checkout) — claimed fix DOES NOT REPRODUCE

Verified by a separate session on `C:\Users\ormas\dev\simple` at HEAD
`5998bfa5e94` (working tree clean for `src/compiler_rust`). Binary identity:
the seed was REBUILT from HEAD with `cargo build --release --bin simple`;
cargo could not replace the locked `target/release/simple.exe` (12:10:26,
PREDATES both fix commits — stale, do not verify against it), so the real
artifact is `src/compiler_rust/target/release/deps/simple.exe`
(38,715,392 bytes, 2026-09-01 12:21:53). That binary contains both commits'
code (the `SIMPLE_DEBUG_WBMA` trace prints added in `5998bfa5e94` are live).

Observed with that fresh binary (verdict lines verbatim):

```
test/01_unit/lib/common/bytes/ints_spec.spl:             11 total,  9 passed, 2 failed
test/01_unit/lib/common/bytes/bytes_foundation_spec.spl:  6 total,  5 passed, 1 failed
test/01_unit/lib/common/bytes/span_spec.spl:             11 total, 11 passed, 0 failed
test/01_unit/lib/common/bytes/bits_spec.spl:             13 total, 13 passed, 0 failed
test/01_unit/lib/common/compress/typed/deflate_typed_spec.spl: 37 total, 37 passed, 0 failed
test/01_unit/lib/common/crypto/typed/ctypes_spec.spl:    31 total, 31 passed, 0 failed
```

The three failures are byte-identical to this record's ORIGINAL pre-fix
evidence ("U16le stores", "U16be stores", "U32be + U32le ... CRC";
`expected 0 to equal 190`). Minimal 2-test spec isolates the shape:

```
✗ chained store persists      (U16le.of(0xBEEF).store(b) -> b.len()==0)
✓ decomposed store persists   (val u = U16le.of(0xBEEF); u.store(b2) -> 2)
```

So at HEAD on this machine the chained-`MethodCall`-receiver write-back is
still lost; the patterns.rs branch either is not reached or does not fire
for this shape here. Hypothesis (one line, unproven): the fix was verified
against uncommitted working-tree state — `5998bfa5e94`'s own message says
pieces "had dropped out of the working tree" in that shared checkout.
`SIMPLE_DEBUG_WBMA=1` shows `store` never reaching the traced write-back
path (only plain-fn `[wbma-enter]` lines appear).

Also re-measured, same binary:
- `run` lane on the minimal repro: still SIGSEGV (rc=139) — matches the
  still-open half above.
- `macho_writer_spec.spl`: ERROR `Cannot resolve module:
  compiler.backend.native.macho_writer`, executed=0 — PRE-EXISTING on this
  machine (identical error on the 2026-08-24 seed), unrelated to ByteBuffer
  (that spec uses elf_writer.spl's own local `struct ByteBuffer`).

## Blast-radius audit of struct->class (same session) — change itself is CLEAN

Enumerated all 40 `ByteBuffer`-referencing files. Three distinct types share
the name: (1) lib `span.spl` ByteBuffer (the changed one); (2)
`src/compiler/70.backend/backend/native/elf_writer.spl:192` local `struct
ByteBuffer` (functional style, out of scope); (3) `perf_sugar_spec.spl`
local `class ByteBuffer` (out of scope). Real users of (1): bits.spl,
ints.spl, deflate_typed.spl, bytes `__init__` facade, and 5 specs;
lzma2_typed/roaring/search-types import it but have zero use sites.

Classification: every use site is category (a) — single-owner accumulator or
intended-visible parameter mutation. Zero category (b) (copy-relying) sites:
no `ByteBuffer` struct/class fields anywhere, no collection storage, no
buffer-to-buffer assignment in product code, and ByteBuffer is append-only
(`push_*`) or rebinding (`clear` sets `self.buf = []`), so a frozen span can
never observe changed bytes inside its window. Empirically confirmed
(test lane, fresh seed): freeze()/to_bytes() snapshots stay independent of
later pushes (1/1), and `var b2 = b1; b2.push_u8(...)` still COPIES in the
interpreter even for a class (`b1.len()` stays 1) — so no aliasing hazard
via assignment either (note: that is an engine-semantics observation worth
its own scrutiny — class assignment appears to remain value-copy in the
interpreter).

Chained-shape sweep: `grep -rnE '\)\.(store|push_span|push_bytes|push_u8|push_byte|update)\('`
over `src/lib` + `src/compiler` = 0 hits — the still-broken chained shape
exists only in the two spec files, not in product code.

Status: struct->class change verified clean (platform-neutral, pure .spl, no
Windows-conditional code touched). The interpreter fix's verification claim
is REOPENED: ints_spec 9/11 and bytes_foundation 5/6 at HEAD here.
