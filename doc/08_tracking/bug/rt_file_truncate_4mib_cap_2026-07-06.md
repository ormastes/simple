# rt_file_truncate caps extend at 4 MiB via the self-hosted binary
## RESOLVED 2026-11-25 — cap verified gone end-to-end on the deployed binary

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Date:** 2026-07-06
**Area:** runtime, self-hosted interpreter extern marshalling, SimpleOS image build
**Status:** ARCHITECTURAL-OPEN — final terminal-status pass 2026-08-10
re-confirms the 2026-08-09 finding: `rt_file_truncate` at
`src/compiler_rust/compiler/src/interpreter_extern/file_io.rs:1047` still
has no visible 4 MiB clamp (`file.set_len(size)` uses the full 64-bit value),
but this cannot be confirmed end-to-end because the fix/diagnosis surface
(`extract_path`'s `Value::Str`-only match plus the truncate path itself) is
entirely inside `src/compiler_rust/**`, out of edit scope for this pass, and
the unrelated `argument 0 must be a string path` marshalling failure still
blocks any fresh repro in this environment. Left OPEN, unmodified.

## Symptom

`rt_file_truncate` silently caps a file-extend truncate at 4 MiB
(4194304 bytes) when run through the self-hosted `bin/simple` binary.
Writing a few bytes and then truncating up to 32 MiB yields a file of
exactly 4194304 bytes instead of 33554432.

## Minimal repro

```text
open a fresh file
write 3 bytes
rt_file_truncate(fd, 32 * 1024 * 1024)   # request 33554432
stat(file).size  ->  4194304             # capped at 4 MiB, not 32 MiB
```

## Root cause (narrowed)

The native C `ftruncate` path is uncapped: `runtime_native.c:2644`
forwards the requested length straight to the OS `ftruncate`. Since the
native path is correct, the 4 MiB ceiling is introduced in the
self-hosted interpreter's extern marshalling for `rt_file_truncate`
(the length argument is clamped/truncated before the native call), not
in the runtime itself.

## Impact

Blocks the FAT flat-bake of large SimpleOS images: baking a rootfs or
ESP larger than 4 MiB via `rt_file_truncate` produces a truncated image
that fails to mount / contains no room for staged payloads. This sits on
the SimpleOS installer/image-build path.

## Workaround

Use coreutils `truncate` (e.g. `truncate -s 32M image.img`) to pre-size
large images instead of `rt_file_truncate` until the interpreter
marshalling cap is fixed.

## Re-verification (2026-08-09, parallel bug-list pass)

Read current `rt_file_truncate` at
`src/compiler_rust/compiler/src/interpreter_extern/file_io.rs:1047-1076`: it
takes the size arg as `u64` (handling both `Value::Int` and `Value::UInt`,
per an in-tree comment referencing a *different*, already-fixed bug —
`doc/08_tracking/bug/disk_image_fat32_builder_defects.md` #2) and calls
`file.set_len(size)` with the full 64-bit value — **no 4 MiB clamp is present
in the source today.**

Attempted a fresh `.spl` repro via the deployed binary
(`bin/simple`, currently the Rust seed per `--version`) calling
`rt_file_truncate` through a local `extern fn` declaration. The repro did not
reach the truncate cap question at all: every extern file-I/O call in this
environment (including plain `rt_file_write_bytes`) failed with
`file_io: argument 0 must be a string path` from
`interpreter_extern/file_io.rs`'s `extract_path`, which pattern-matches only
`Value::Str` — an apparently unrelated `text` vs `Value::Str` marshalling
mismatch for top-level extern calls in this build/environment, not a
truncate-specific defect. This blocks confirming the cap is actually gone
end-to-end.

**Status kept OPEN**, but re-scoped: (1) the fix location is
`src/compiler_rust/compiler/src/interpreter_extern/file_io.rs`, which is
out of bounds for this pass (`src/compiler_rust/**` must never be edited
here); (2) the specific 4 MiB clamp described above is not visible in
current source, so this may already be fixed or may have been masked by the
separately-observed `argument 0 must be a string path` extern-marshalling
issue that blocks any repro in this environment. Needs a session with
`src/compiler_rust` edit scope to (a) fix/diagnose the `extract_path`
`Value::Str`-only match generally, then (b) re-run the original 32 MiB
truncate repro end-to-end to confirm the cap is gone.

## Next Check

Trace the `rt_file_truncate` extern signature/marshalling in the
self-hosted interpreter, confirm where the length is clamped to 4 MiB,
and widen it to the full 64-bit length the native `ftruncate`
(`runtime_native.c:2644`) already accepts.


## Resolution 2026-11-25 — end-to-end repro now passes; closing

The 2026-08-09 re-verification showed the 4 MiB clamp absent from
`src/compiler_rust/compiler/src/interpreter_extern/file_io.rs` source but could
not confirm end-to-end because extern file-I/O calls failed with
`argument 0 must be a string path` in that environment. Both halves are now
closed on the current deployed binary (`bin/simple.exe`, Rust seed
v1.0.0-rc.1, build-commit `1343b77bbaa`, Windows host):

Probe (exact original repro shape — write 3 bytes, truncate up to 32 MiB):

```simple
extern fn rt_file_truncate(path: text, size: u64) -> bool
extern fn rt_file_write_bytes(path: text, data: [u8]) -> bool
extern fn rt_file_size(path: text) -> i64

fn main():
    val p = "C:/.../trunc_probe.img"
    val w = rt_file_write_bytes(p, [104, 105, 33])
    val ok = rt_file_truncate(p, 33554432)
    print("truncate ok: {ok}")
    print("size: {rt_file_size(p)}")
```

Measured output:

```text
write ok: true
truncate ok: true
size: 33554432
```

`ls -l` on the produced file confirms 33,554,432 bytes — the requested 32 MiB,
not the 4,194,304-byte cap. The `argument 0 must be a string path` marshalling
failure that blocked the 2026-08-09 repro also no longer occurs: the `text`
path argument marshals correctly through `extract_path`. No 4 MiB ceiling
exists on this lane; the FAT flat-bake blocker described above is gone.
Status: RESOLVED.
