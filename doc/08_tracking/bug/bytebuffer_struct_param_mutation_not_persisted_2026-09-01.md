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

## Root cause (not yet located)

Not investigated further — this is interpreter/runtime struct-parameter-passing
semantics, orthogonal to `src/lib/common/bytes/*`. Flagging per
`.claude/rules/testing.md` guidance rather than attempting a compiler-internals
fix in scope of a test-triage pass.

## Not fixed here

Per CLAUDE.md testing rules, the two reproducing specs (`ints_spec.spl`,
`bytes_foundation_spec.spl`) are left RED and reported as genuine failures
rather than weakened. `.spl` test files not modified.
