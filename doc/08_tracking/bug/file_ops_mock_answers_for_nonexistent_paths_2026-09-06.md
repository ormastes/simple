# `std.nogc_sync_mut.file_system.file_ops` is a MOCK: `file_exists` is true for any path, reads return "mock file content"

**Date:** 2026-09-06
**Status:** OPEN — worked around at one call site, root cause not fixed
**Severity:** High — a caller that trusts these functions silently processes
fabricated data with a success exit code.
**Component:** `src/lib/nogc_sync_mut/file_system/file_ops.spl`
(and its twin `src/lib/nogc_async_mut/file_system/file_ops.spl`)

## Symptom (measured)

```
file_exists("/nonexistent")     -> true
file_read_text("/nonexistent")  -> Option::Some(mock file content: /nonexistent)
```

Both from a program whose only import of these names is
`use std.nogc_sync_mut.file_system.file_ops.{file_read_text, file_exists}`.

Two distinct problems in one:

1. **Fabricated success.** There is no error path to detect. A missing file is
   indistinguishable from a present one, and the "content" is a synthesised
   string containing the path.
2. **The `Option` leaks into text.** `file_read_text` returns `text?`, and
   interpolating the result yields the literal `Option::Some(...)` rather than
   the content. Callers that pass the value straight through — rather than
   pattern-matching it — propagate the wrapper.

## Cause

`src/lib/nogc_sync_mut/file_system/file_ops.spl:21-32`

```simple
fn file_read_text(path: text) -> text?:
    if path == "" or not file_exists_mock(path):
        return nil
    Some("mock file content: " + path)
```

and `file_exists_mock` (`:204-207`) returns true for every non-empty string.
These are stubs that were never replaced.

## Why this is worse than an ordinary stub

The same file already carries a warning about a related incident:

> `file_read_bytes` intentionally does NOT live here. […] because the flat
> function registry is keyed on NAME ALONE […] it could hijack any call site in
> an import closure that happened to include this module and serve a hardcoded
> "Hello" for every path.
> — see `doc/08_tracking/bug/file_read_bytes_has_six_definitions_with_three_return_types_2026-08-09.md`

`file_read_text` and `file_exists` have exactly that shape and were left in
place. Which definition a given call site resolves to therefore depends on its
import closure, not on what it wrote. Observed directly in this session:
`src/app/devhub/config.spl` imports these very names from this very module and
**does** read real config files, while a small probe importing the identical
names got the mock. Same spelling, different behaviour, decided by the closure.

That makes the blast radius unknowable by reading source: `config.spl`
(`load_config`, `load_auth_token`) reads credentials and configuration through
these names. It currently works. Nothing in the type system or the import
statement guarantees it keeps working.

## How it was found

Wiring `gh pr create --body-file <path>` in `src/app/devhub/cmd_git.spl`. The
guard "refuse an unreadable body file rather than open a pull request with an
empty body" never fired, because `file_exists` said the missing file was there
and the reader handed back `Option::Some(mock file content: /nonexistent)`.
Left unnoticed, that opens pull requests whose description is the literal
string `mock file content: /path/to/body.md`.

## Workaround applied (this change)

`cmd_git.spl` reads through **`app.io.mod.{file_read, file_exists}`**, verified
honest against the same inputs on 2026-09-06:

| input | `app.io.mod` |
|---|---|
| `file_exists("/nonexistent")` | `false` |
| `file_exists("/etc/hostname")` | `true` |
| `file_read` of a real file | real content |
| an empty file | `exists=true`, content `""` — distinguishable from missing |

Pinned by `test/01_unit/app/devhub/cmd_git_spec.spl`, which asserts the refusal
message never contains `mock file content` — so a future switch back to the
mock module fails the spec instead of shipping.

## Suggested fix for the owner

1. Delete the mock bodies and back `file_read_text`/`file_exists` with the real
   syscalls, or delete the two functions from this module entirely and let call
   sites resolve to the honest implementation — the treatment already applied
   to `file_read_bytes` in this same file, for this same reason.
2. Audit `config.spl`'s use of these names, since it reads auth material
   through them and today only works by resolution luck.
3. Longer term this is the flat name-keyed function registry again; the
   2026-08-09 record is the tracking item for that.
