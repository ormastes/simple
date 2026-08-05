# `rt_io_file_*`: interpreter gap fixed this session; native/JIT still returns the RT_KEEP stub pending a runtime redeploy

Date: 2026-08-05
Lane: IO-REWIRE follow-up
Status: PARTIALLY FIXED. Interpreter engine now works end-to-end and is
verified with a real disk round-trip. Native/JIT engine is UNCHANGED —
confirmed still stubbed, with a precise repro below. This is expected per the
ordering hazard already on record in `stubs.rs` and the original bug doc; it
is not a new defect, it is a status update plus a concrete positive
confirmation (the earlier report predates any verification run).

Supersedes/updates:
`doc/08_tracking/bug/rt_io_file_family_undefined_stubbed_silent_data_loss_2026-08-05.md`
(that doc's "native symbols undefined" and "interpreter fails closed" claims
were both true at the time; the native symbols were then implemented in
`runtime/src/value/sffi/file_io/io_file.rs` (commit `31c6287af87`), but two
things that report did not check are checked here: (1) whether the
interpreter registry gap was ever closed — it hadn't been until this session
— and (2) whether the native/JIT path was actually verified working after the
symbols were implemented — it wasn't; this doc is the first real run of
either engine against real disk I/O).

## What this session did

1. Read `src/lib/nogc_sync_mut/io/file.spl` and
   `runtime/src/value/sffi/file_io/io_file.rs` to confirm the native runtime
   implementation (16 `rt_io_file_*` symbols: open/read/read_all/read_line/
   write/write_all/seek/flush/close/set_permissions/meta_size/meta_flags/
   meta_modified/meta_created/exists/delete) is real, not a stub.
2. Found `test/01_unit/lib/io/rt_io_file_family_check.spl` (landed in the same
   commit as the native fix, `31c6287af87`) already existed but had never
   actually been run: it called `wh.write_text(...)` expecting `Ok(n)` (a byte
   count) and `rh.read_text(3)` (a sized read) — neither exists on the real
   `FileHandle` API (`write_text` returns `Result<(), IoError>`;  `read_text`
   takes no size argument). Fixed the check to call only real methods.
3. Ran the fixed check under `SIMPLE_EXECUTION_MODE=interpret` and hit
   `unknown extern function: rt_io_file_delete` — the interpreter's static
   extern registry (`src/compiler_rust/compiler/src/interpreter_extern/`)
   never had entries for this family; only the native runtime symbols existed.
   Added `interpreter_extern/io_file.rs` (16 functions operating on real OS
   fds via `File::from_raw_fd`/`into_raw_fd`, mirroring the native
   implementation) and registered all 16 in
   `interpreter_extern/mod.rs`'s `insert_simple!` table.
4. Rebuilt the Rust seed from an isolated source snapshot (see "Build hazard"
   below) and re-ran the check under `SIMPLE_EXECUTION_MODE=interpret`:

   ```
   VERDICT: PASS rt_io_file family works
   ```

   This is a real disk round-trip: write 10 bytes, confirm `File.exists`,
   read back and compare content, seek to 3 distinct `SeekFrom` variants and
   confirm 3 distinct absolute positions (not collapsed to one value, which
   is what an all-stub family would produce), read 3 bytes after seeking to
   offset 4 and confirm they are exactly `"456"`, and confirm `size() == 10`.

## What's still broken: native/JIT

Running the same check via `bin/simple run` (no `SIMPLE_EXECUTION_MODE`, i.e.
JIT — see `.claude/rules/testing.md` "`run` and `test` are DIFFERENT
ENGINES") fails immediately:

```
VERDICT: FAIL rt_io_file family broken (open WriteOnly failed)
```

Minimal repro (`extern fn rt_io_file_open(path: text, mode: i64) -> i64` called
directly with `mode=1` i.e. WriteOnly on a fresh path) returns `fd=-1`.
Confirmed via `strace -f -e trace=openat,open` across the whole process tree:
**zero** `openat`/`open` syscalls reference the target path at all. This rules
out a permissions/environment problem (a plain `touch` on the same path
succeeds) and confirms the call never reaches the real Rust implementation —
it is still being served by the RT_KEEP fabricated stub.

Root cause, already on record and unchanged: `stubs.rs:195-221` keeps all 12
of the fd-level `rt_io_file_*` symbols (`open, read, read_all, read_line,
write, write_all, flush, seek, close, set_permissions, exists, delete`) in
`RT_KEEP` with this comment:

> Implementations now exist in `runtime/src/value/sffi/file_io/io_file.rs`
> (verified defined via `nm`), but a native link still resolves against the
> *deployed* `target/bootstrap/libsimple_runtime.a`, which predates them.
> Removing an entry before that archive is rebuilt turns every native build
> into a hard failure, so the removal must follow the runtime redeploy, never
> precede it.

That redeploy has not happened. `target/bootstrap/libsimple_runtime.a` is the
archive both `native-build` and (per this session's evidence) `run`/JIT link
compiled `.spl` programs against; it predates `io_file.rs` and therefore has
none of these 16 symbols, so native links keep falling through to the
RT_KEEP stub regardless of interpreter-side fixes.

## Why this session does not attempt the redeploy

Per `.claude/rules/bootstrap.md`, dropping `RT_KEEP` entries and redeploying
`target/bootstrap/libsimple_runtime.a` is a **T3 — full bootstrap** operation
("ONLY when the compiler itself changed ... or as the final pre-goal-complete
gate"), not a small scoped fix. It also has a hard ordering requirement (the
archive must be rebuilt *before* the stub entries are removed, "never the
reverse" per both `stubs.rs` and the original bug doc) and this repo's working
copy has multiple other lanes actively mutating `src/compiler_rust` and
`src/runtime` concurrently (observed directly: a concurrent `cargo build
--release -p simple-driver` from another session, and a third lane actively
rewriting `src/runtime/runtime_native_gpu_stub.c` mid-build, which twice broke
this session's own seed rebuild with a torn-file C syntax error until an
isolated snapshot copy of the source tree was used to build safely). A full
bootstrap + redeploy landed here today, on top of that, without dedicated
verification time, risks shipping a wrong `target/bootstrap` artifact to every
other concurrent lane.

## Next step (not done here)

1. Full bootstrap: `scripts/bootstrap/bootstrap-from-scratch.sh
   --full-bootstrap --deploy` (or the incremental T1/T3 path once the WC is
   quiet), producing a fresh `target/bootstrap/libsimple_runtime.a` that
   carries all 16 `rt_io_file_*` symbols.
2. Verify with `nm -g --defined-only target/bootstrap/libsimple_runtime.a |
   grep rt_io_file` (expect 16, currently 0 for the fd-level dozen; `exists`/
   `delete` may already be present via a different path — check before
   assuming zero).
3. Only then drop the 12 listed entries from `RT_KEEP` in `stubs.rs:209-221`.
4. Re-run `test/01_unit/lib/io/rt_io_file_family_check.spl` under `bin/simple
   run` (JIT) and `bin/simple native-build` (AOT) and confirm both print
   `VERDICT: PASS`. Until then, native/JIT is NOT trustworthy for this API —
   `File.write`/`FileHandle.open` degrade silently exactly as the original
   report described.

## Files touched this session

- `src/compiler_rust/compiler/src/interpreter_extern/io_file.rs` (new) —
  interpreter-mode implementations of all 16 symbols.
- `src/compiler_rust/compiler/src/interpreter_extern/mod.rs` — module
  declaration + 16 `insert_simple!` registrations.
- `test/01_unit/lib/io/rt_io_file_family_check.spl` — fixed to call the real
  `FileHandle`/`File` API surface instead of a surface that never existed.
