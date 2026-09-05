# Source-text guard specs went red *because* the defect they guard was fixed

**Status:** FIXED for the three specs found; filed for the anti-pattern
**Found:** 2026-08-04
**Severity:** medium — two of the three demanded a code pattern the source
itself documents as non-functional, so the obvious way to make them green is to
reintroduce a fail-open parse of attacker-supplied input

## Symptom

Three specs under `test/01_unit/lib/nogc_sync_mut/` assert on the *text* of a
product file rather than on its behaviour. All three were red:

| spec | before |
|---|---|
| `http_server/range_numeric_guard_spec.spl` | 0 passed, 1 failed |
| `stomp/subscribe_content_length_numeric_guard_spec.spl` | 0 passed, 1 failed |
| `compression/gzip_inflate_negative_offset_guard_spec.spl` | 0 passed, 1 failed |

```sh
$ SIMPLE_TIMEOUT_SECONDS=0 bin/simple test --no-cache --no-cover-check \
    test/01_unit/lib/nogc_sync_mut/http_server/range_numeric_guard_spec.spl
  ✗ defaults malformed range numeric parsing
    expected subject to be truthy, got false
```

## Root cause

**1 & 2 — the pinned string is the OLD, BROKEN spelling.** The Range spec
required the source to contain `start = start_str.to_int() ?? 0`, and the STOMP
spec required `return value.to_int() ?? nil`. Both patterns are dead code, and
the product files say so at the exact spot:

`src/lib/nogc_sync_mut/http_server/utilities.spl:91-95`

> Fail-CLOSED: a malformed Range must be IGNORED (serve the whole entity, per
> RFC 9110), not coerced to 0. `.to_int() ?? 0` / `?? -1` could never fire --
> `.to_int()` is typed `i64?` but its runtime returns a plain int64_t and
> cannot produce nil, so `"bytes=abc-def"` silently became `"bytes=0-0"`.

`src/lib/nogc_sync_mut/stomp/subscribe.spl:80-82` carries the same note for
`content-length:abc` reading as 0. Both now parse through `try_parse_int`,
which really can report failure, and both fail closed. The specs were never
updated, so each one now demands that a fixed input-validation bug be put back.

**3 — the helper called a matcher as a string method.**
`gzip_inflate_negative_offset_guard_spec.spl` used `source.to_contain(...)`.
`to_contain` is a matcher, not a method on `text`; the method is `.contains()`.
The misuse aborted the example rather than testing anything, so this guard had
never actually run. Underneath it, the pinned signature
`fn deflate_block_parse(data, offset):` had also gone stale — the real one is
`fn deflate_block_parse(data, offset) -> [Any]?:`
(`src/lib/nogc_sync_mut/compression/gzip/inflate.spl:531`) — so even a working
helper would have reported the guard absent while it was present at line 535.

**No product code was wrong in any of the three cases.** All three products are
strictly safer than what their specs demanded.

## Fix applied

Each spec now pins the current, stronger invariant, and keeps a negative
assertion so the coercing spelling cannot come back:

| spec | after |
|---|---|
| `range_numeric_guard_spec.spl` | 3 passed |
| `subscribe_content_length_numeric_guard_spec.spl` | 2 passed |
| `gzip_inflate_negative_offset_guard_spec.spl` | 1 passed (and now actually asserts) |

## The anti-pattern

A source-text guard pins *syntax* while claiming to protect *behaviour*. Its
failure mode is inverted from a normal test: it goes green while the code is
broken as long as the string is present, and red when the code is improved. Two
of the three here were pinning a string the codebase had already proven to be a
no-op.

Where the property is genuinely about shape (a bounds check preceding an
indexed read), the guard should assert the shape at its narrowest — the
presence of the guard clause and the absence of the unguarded spelling — and
never the full signature line, which changes for unrelated reasons like gaining
a return type. Where the property is about behaviour (malformed input is
rejected), the guard should call the function with malformed input, which none
of these three do.

## Also found, not fixed

`test/01_unit/lib/nogc_sync_mut/db/dbfs_engine/zz_probe2_spec.spl` is a
debugging probe that was committed: every line but the last is a `print`, its
only assertion is the tautology `expect(1).to_equal(1)`, and it imports
`nvme_arena_registered_count` from
`std.nogc_sync_mut.db.dbfs_engine.raw_nvme_arena` — a function that exists
nowhere in `src/`. It therefore fails the whole file at load with
``semantic: function `nvme_arena_registered_count` not found``. It is not a
test (a tautological assertion cannot fail), so making it green would mean
inventing an API to satisfy a probe. It needs its author to say whether the
counter was planned or the file is scratch; left alone rather than deleted.
