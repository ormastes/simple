# rt_file_truncate caps extend at 4 MiB via the self-hosted binary

**Date:** 2026-07-06
**Area:** runtime, self-hosted interpreter extern marshalling, SimpleOS image build
**Status:** OPEN

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

## Next Check

Trace the `rt_file_truncate` extern signature/marshalling in the
self-hosted interpreter, confirm where the length is clamped to 4 MiB,
and widen it to the full 64-bit length the native `ftruncate`
(`runtime_native.c:2644`) already accepts.
