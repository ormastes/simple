# HIR cache reuses the wrong physical source owner

The C32 normal runner build reached HIR 218/218 and failed closed with
`cold-hir-module-source-mismatch`, exit 1, before MIR or native objects.
Producer SHA: `f1be42d8724011f89d594024434019b80218c059bd5e4e7ba65331272c5ff7e9`.
Source HEAD: `7ba9185858a6cb2c8dd3235c73ee4d3aa01027b7`.
No actual test cases ran; this producer has no canonical Stage2 admission.

Retained evidence is under
`build/native_probe/phase3-whole-20261011-c06/c32-producer-c32-runner/`
in the preserved `simple-bootstrap-c06-20261011` worktree. The construction
log, result, source/runtime before/after manifests, per-PID RSS trace and
`hir-path-collision-evidence.json` bind this observation. Tree peak RSS was
2641628 KiB, below the enforced 6835937 KiB cap.

Two admitted sources, `src/lib/nogc_async_mut/env/mod.spl` and
`src/lib/nogc_sync_mut/env/mod.spl`, have identical bytes with SHA256
`83bea209d4c2355aa67b8b445355043fb5225d68e9e64d9bc606d4c7cab84c8f`.
They share the closure digest and non-entry role. The old cache key omitted
the physical path, so both selected
`5465e00f776d1c289cda373c8432adb3e98ecaba36864d11f9d10aa5829728c4.hir`.
Its encoded HIR path belongs to the async source. Reusing it for the sync
source violates the retained source identity contract.

The first diagnostic printed a missing `std` alias of an earlier physical
source. Receipt validation skips that alias; diagnostic deduplication is
repaired separately. Therefore the original printed diagnostic alone does
not prove that the cache collision was the first validator failure. The
independent cache key and retained payload evidence prove the collision.

Repair: version the key identity and include a digest of the normalized full
physical source path. Preserve the frozen snapshot prefix, compiler/header
admission, content and closure digests, entry role, environment and codec
identity. Old artifacts stay intact but cannot match the new key. Physical
aliases retain one surface lowering; logical names already participate in
the closure digest. Never rewrite a decoded module path to hide a mismatch.

The new regression uses two tracked identical-byte fixture files and calls
the real file-based cache key API. It also checks stable repeat keys, entry
role separation and missing-source rejection. These tests are written but
unexecuted until a functioning pure-Simple runner is available. Compiler
construction and the normal runner replay remain required.
