# cache host global caps_lock held across fsync and 64 MB pread plus verify

Severity: P1. Location: src/runtime/runtime_cache_host_authority_v1.c:469,472-478

## Interleaving
Thread A calls rt_cache_host_pread_receipt_v1 on a 64 MB object. It holds caps_lock while preading the whole object, then re-preads and memcmp's it a second time in 4 KB chunks. Thread B (any open, size, write_temp or publish on any capability) blocks on caps_lock for the whole duration. rt_cache_host_publish_noreplace_v1 likewise holds caps_lock across fsync(c->fd), fchmod and the rename step, so one slow disk sync stalls every reader and writer in the process.

find_cap returns a raw pointer valid only under the lock, so the lock cannot simply be dropped today; a refcount or per-cap mutex is needed first.

## Fix
Per-cap refcount plus per-cap lock; the global lock guards only the list. Do fsync and pread outside it.

## Stress spec
Thread 1 loops pread_receipt on a 64 MB cap; thread 2 times 10k rt_cache_host_size_v1 calls on a different cap; assert p99 under 5 ms.
