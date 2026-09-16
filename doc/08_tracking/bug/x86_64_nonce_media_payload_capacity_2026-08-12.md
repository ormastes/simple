# x86_64 nonce media exceeds configured FAT image capacity

## Status

Source fix present; fresh build/live proof pending. The 2026-08-12 rebuild session exhausted three distinct capacity cycles
(128 MiB, 256 MiB, and 512 MiB) without producing an x86_64 nonce-capable
image. Do not repeat those unchanged commands in the same session.

## Evidence

- `/mnt/data/.simple/qemu/artifacts/sosix-qemu/rebuild/nonce-five-20260812T024500Z/x86_64/image-build.log`
- `/mnt/data/.simple/qemu/artifacts/sosix-qemu/rebuild/nonce-x86-fix-20260812T025000Z/x86_64/image-build.log`
- `/mnt/data/.simple/qemu/artifacts/sosix-qemu/rebuild/nonce-x86-64-size2-20260812T030000Z/x86_64/image-build.log`

All terminate with `disk image too small for payload set`. Kernel construction
succeeds. Unlike the other rows, the x86_64 wrapper stages the available
117 MiB `clang_static` payload in addition to the pinned font/tool bundle.

## Diagnosed root cause and bounded fix

The FAT geometry calculation was not the cause. `make_os_disk.shs` treats the
Simple toolchain payload as optional and validates it only when explicitly
selected, but `make_os_disk.c::read_simpleos_simple_payload` independently
searched host `build/bootstrap/stage3/simple_simpleos` and release locations.
When such an unrelated host artifact existed, the builder silently staged it
across thirteen independent FAT chains: seven raw roles and six SMF roles.
FAT32 has no hard links, so this amplification is real; the configured image
minimum therefore changed with unselected host state and could exceed 512 MiB.

The C builder now stages only the wrapper-selected `SIMPLEOS_SIMPLE_BINARY`.
Implicit stage3/release discovery is removed. Large/duplicated allocations are
attributed by guest path, and a capacity failure emits one bounded receipt with
payload name, payload bytes, required clusters, already allocated clusters,
capacity clusters, cluster bytes, and derived `minimum_image_mb`. The static
contract records all thirteen Simple roles so a future explicit large payload
remains diagnosable rather than being hidden by another size guess.

No rebuilt image or QEMU result has validated this source fix. The earlier
three logs remain failure evidence only.

## Unblock condition

In a fresh session, perform exactly one x86_64 rebuild with the admitted
compiler and current source. If it succeeds, perform exactly one canonical
Linux x86_64 QEMU run and retain the correlated nonce/list/program receipt. If
capacity still fails, stop on the new attributed receipt; do not resize or
retry.

## Fresh-session resume

Start a guarded fresh session through:

```bash
bin/codex exec -C /home/ormastes/dev/pub/simple 'Resume doc/08_tracking/bug/x86_64_nonce_media_payload_capacity_2026-08-12.md. Use the admitted pure-Simple compiler and current explicit-only payload selection. Run exactly one `sh scripts/check/rebuild-sosix-qemu-media.shs --run --rows x86_64`; if and only if it succeeds, run exactly one canonical Linux x86_64 matrix/QEMU row with a fresh nonce. Retain build, image, serial, hashes, and capacity receipt. Stop after either failure; do not resize or retry.'
```
