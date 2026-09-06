# Correction: mod_stub local file-op defs were ALL dead, not seed-registry-rescued

Date: 2026-08-07
Status: CLOSED (not reproducible)
Status re-verified 2026-08-17 by source inspection (triage shard 02).
Area: lib / module resolution

## What the commit message got wrong

Commit `09900bfaa62` ("fix(lib): drop dead mod_stub file-op duplicates that call
undeclared rt_* externs") removed five local file-op helpers from
`src/lib/nogc_sync_mut/io/mod_stub.spl` and `src/lib/gc_async_mut/io/mod_stub.spl`.
The removal is correct. **The explanation in the message is not.**

The message claims that `file_append`, `file_modified_time`, `file_remove` and
`file_size` "did bind — and worked only because the seed interpreter resolves
`rt_*` by a global intrinsic registry rather than requiring a module-local
declaration."

That was inferred from a passing behavioral probe, never tested directly. A
sentinel probe afterwards disproved it.

## The sentinel probe

Against the **pre-fix** file content, the local `file_size` body was replaced
with a constant sentinel:

```
fn file_size(path: text) -> i64:
    -999
```

A caller doing `use std.nogc_sync_mut.io.mod_stub.{file_size}` on a 16-byte file
then printed:

```
SIZE 16
```

Not `-999`. The local definition was never invoked. Engine: seed
(`bin/simple run`, which self-identifies as a bootstrap seed).

## Corrected finding

**All five** local defs were dead code, exactly like the `file_hash_sha256` one
that was already proved dead by digest comparison — not four live-but-masked
plus one dead. The commit was therefore pure duplicate removal with no
behavioral surface at all, which is a stronger and simpler result than claimed.

The global-intrinsic-registry mechanism plays no part in this and should not be
cited from that commit message.

## Open sub-question

Why the re-export wins is only partly explained. `file_hash_sha256` IS in the
`export use std.<tier>.io.file_ops.{...}` list at the top of the file, so it
winning is unsurprising. But `file_size` was **not** in that list and still
resolved to the `file_ops` implementation rather than the module-local `fn`.

So importing a name from `io.mod_stub` can yield a sibling module's definition
even when `mod_stub` defines that name locally and does not re-export it. That
is a module-resolution behaviour worth pinning down on its own; it is not
investigated here, and the `warning: unresolved call` /
`[WARN] Failed to load imported types` diagnostic families are owned by other
lanes.

## Unrelated finding surfaced during this work

`src/app/sffi_gen.templates/bootstrap_sffi.txt:282` defines a third arm of
`rt_file_hash_sha256` that returns **file size as hex**, not a digest:

```rust
fs::metadata(p.as_ref()).ok().map(|m| format!("{:016x}", m.len()))
```

The two live Rust arms are genuine SHA256
(`runtime/src/value/sffi/file_io/file_ops.rs:491` via `sha2`,
`compiler/src/interpreter_extern/file_io.rs:145` via `ring`). The template arm
is already tracked as
`doc/05_design/ml/slang/fs_requests/FS-REQ-003-sha256-runtime-primitive.md`
("stub only — returns a 16-char..."). Left as-is: it is Rust, and it belongs to
that request.
