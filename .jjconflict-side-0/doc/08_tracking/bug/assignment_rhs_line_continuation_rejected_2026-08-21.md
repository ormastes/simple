# Parser rejects an assignment whose RHS is on the next line

- Date: 2026-08-21
- Area: compiler / parser (grammar gap)
- Severity: medium — the failure is at MODULE level, so one such line takes down
  every spec that transitively imports the file. Three `http_server` specs went
  red this way and the cause was three files away from any of them.
- Status: OPEN. Filed rather than silently normalised, per CLAUDE.md ("When a
  short, safe grammar or compact expression form fails … fix it or record a
  concrete bug/feature request instead of silently normalizing the workaround").
  The call sites were joined onto one line to unbreak the build; that is the
  workaround, this doc is the record.

## Repro (6 lines)

```simple
fn main():
    var a = [0, 0, 0]
    var i = 0
    a[i] =
        7
    print("v=" + a[0].to_string())
```

```
error: compile failed: parse: Unexpected token: expected expression, found Newline
```

Same statement on one line (`a[i] = 7`) parses and runs. Verified on the
deployed aarch64 binary (2026-07-25) **and** on a seed built from `origin/main`
at `7cc8bddb03ef` — so this is not binary age, it is the current grammar.

## Where it bit

`src/lib/common/net/tls_application_record_stream_v1.spl:199-200`, as landed by
`4b88aebf00`:

```simple
self.storage[self.ring_index(write_offset + incoming_index)] =
    incoming[incoming_index]
```

The file never parsed. Because the failure is at module load, the visible
symptom was three unrelated specs failing with a `1 total, 0 passed, 1 failed`
shape (a load failure, not an assertion failure):
`worker_static_file_spec`, `async_dynamic_dispatch_spec`,
`worker_wire_shutdown_spec`.

## Neighbouring gaps found in the same sweep

Two more module-level parse failures landed in the same upstream commit. Both
are already-documented limitations rather than new grammar gaps, but they share
the blast radius and are worth listing together, because all three present
identically (a spec that never loads):

1. **`pass` used as an identifier** —
   `src/lib/nogc_async_mut/http_server/worker_connection_extensions.spl:428`
   had `var pass = 0`, giving
   `parse: Unexpected token: expected pattern, found Pass`. `pass` is a keyword
   token in the lexer. Note `.claude/rules/language.md`'s reserved-keyword list
   names `pass_todo` / `pass_do_nothing` / `pass_dn` but **not bare `pass`** —
   the list is incomplete and should be corrected. Fixed by renaming to
   `pass_index`. Confirmed on a fresh seed, so this is not binary age either.
2. **Multi-line boolean without parentheses** —
   `src/lib/nogc_async_mut/http_server/server.spl:462-463` continued an `if`
   condition after a trailing `or` with no wrapping parens, giving
   `parse: Unexpected token: expected identifier, found Dot`.
   `.claude/rules/language.md` already documents that multi-line booleans must
   be parenthesised; fixed by wrapping.

## Suggested fix

Accept a line continuation after `=` in assignment (and augmented assignment),
consistent with the existing support for continuations inside parentheses and
in multi-line call arguments. If the intent is that it should *not* be
supported, the diagnostic should say so at the offending line rather than
surfacing as `expected expression, found Newline`, and the reserved-keyword
documentation should be corrected in the same pass.

The deeper reportability problem is shared by all three: a module-level parse
failure is attributed to the SPEC that imported it, not to the file that failed,
so the reader sees `worker_static_file_spec: 1 total, 0 passed, 1 failed` and
has to chase the real file by hand. Surfacing the failing file and line in the
spec verdict would have made all three self-diagnosing.
