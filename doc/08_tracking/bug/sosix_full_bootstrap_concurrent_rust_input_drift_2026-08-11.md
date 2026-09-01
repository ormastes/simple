# SOSIX release lineage blocked by concurrent Rust input drift

**Date:** 2026-08-11  
**Status:** open; fail-closed provenance guard worked

After runtime C syntax became clean, one bounded command ran with seed fallback
forbidden:

```text
env SIMPLE_NO_STUB_FALLBACK=1 scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy
```

The run rebuilt the Rust bootstrap compiler, native-all package, and runtime
support offline. It then exited 1 during compiler backfill:

```text
error: Rust inputs changed during full bootstrap; refusing to publish a stale seed
```

This is not a compiler diagnostic and must not be bypassed: another session
changed `src/compiler_rust` while the long build was active, so publishing its
candidate would break source lineage. Retained logs are under
`build/bootstrap/logs/x86_64-unknown-linux-gnu/`, with the final evidence in
`rust-compiler-backfill-build.log`.

Resume only from a stable Rust input snapshot. Reuse the cache, keep
`SIMPLE_NO_STUB_FALLBACK=1`, and run one full bootstrap/deploy attempt. Do not
launch authoritative QEMU rows until the deployed binary identifies as the
pure-Simple self-hosted compiler and its source tree is unchanged.
