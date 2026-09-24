# Native linker runtime-object staging optimization

## Scope and retained baseline

The retained tiny-build diagnostic row reports 1.32 s wall time, 1.3 s in the
reported link phase, 32,440,320 bytes maximum RSS, and an invalid artifact with
652 fabricated unresolved stubs. It proves that linker preparation/linking is
the dominant observed phase, but it is not a valid end-to-end compile-speed
baseline and is not used to claim a measured speedup.

## Audit

- The normal hosted path constructs one linear object list: user objects,
  runtime inputs, optional native-all, entry object, then external providers.
- The runtime cache key is exact for runtime object generation: runtime C/header
  content, C compiler version, target/host architecture, optimization level,
  ABI policy, dynload provider selection, Stage-4 legacy selection, object
  format, and relevant vector flags. A changed input selects another directory.
- A complete warm hit formerly copied every immutable cached object to a
  PID-scoped temporary object. The default inventory is 30 objects, or 31 when
  the dynload provider is selected.
- Darwin admission then hashes each final link input, snapshots it by digest,
  and rehashes an existing snapshot before reuse. These checks intentionally
  detect mutation/corruption and remain unchanged.
- Mach-O dead stripping and requested symbol stripping are passed together in
  the final linker invocation (`-dead_strip`, optionally `-S -x`); there is no
  redundant post-link strip process to remove.
- A prelinked runtime/provider archive could reduce linker input count, but it
  can change archive-member extraction, weak/duplicate symbol resolution, and
  Stage-4 provider ownership projection. It requires a separate exact
  runtime/provider/toolchain composition receipt and ABI parity suite, so it is
  not introduced by this safe change.

## Change

`runtime_cache_stage_object_v1` attempts an argument-safe hard link from the
immutable exact-key cache object to the disposable PID path. If hard linking is
unsupported or crosses filesystems, it falls back to the previous byte copy.
Cleanup removes only the disposable directory entry; the cache inode remains.
The object bytes, order, target architecture, ABI, linker flags, and provider
selection are unchanged.

## Effect

For a complete warm cache hit on a same-filesystem cache:

| Metric | Before | After |
|---|---:|---:|
| Runtime objects staged | 30 default / 31 with dynload | unchanged |
| Full object-byte copies | 30 default / 31 with dynload | 0 |
| Staging bytes written | sum of runtime object sizes | 0 |
| Final linker executions | 1 | 1 |
| Darwin input hashes/snapshot validation | unchanged | unchanged |

The focused model test proves zero staged bytes on the hard-link path and exact
copy-byte accounting on fallback. No claim is made that the retained invalid
1.3 s link row improved; a rebuilt producer-authenticated compiler is required
for a valid cold/warm native-build measurement.

## Verification

- `test/05_perf/compiler/runtime_object_cache_hardlink_reuse_spec.spl`
- repository optimizer attempted on the touched Simple source; the admitted
  runtime exited 1 with `Error running src/app/optimize/main.spl`, so no
  optimizer success is claimed
- `git diff --check`
