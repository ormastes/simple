# Rust authority fingerprint includes its own generated build outputs

**Status:** fixed in the frozen worktree; focused authority self-test passed;
canonical authority publication and Stage-2 verification pending.
**Observed:** 2026-08-15.

## Exact failure

The final bounded Phase-2-only transaction rebuilt all four Rust authority
members, then exited 1 before publication with:

```text
error: Rust inputs changed during full bootstrap; refusing to publish a stale seed
```

Evidence:

- manifest SHA-256
  `6c041d7a4378b9ec3be2b57a348ab55bd4d73d11192a71741ed95a0c7a57b2a0`,
  27,071/27,071 listed files verified before the build;
- `build/native_probe/stage4-owner-20260815/canonical-phase2-after-rt-file-sync-fix-v4.{log,status,time}`;
- exit 1 after 9m49.41s, maximum RSS 2,701,812 KiB;
- retained generated files under
  `build/native_probe/stage4-owner-20260815/self-generated-fingerprint-drift-v4/`.

No authority was published, the pre-publication marker was never reached,
Stage 2 did not start, the 846-object Stage-2 cache was not consumed, and no
candidate/hash, sanity receipt, receiver receipt, Stage 3, or Stage 4 exists.

## Root cause

`bootstrap_stage3_seed_inputs_fingerprint` in
`scripts/check/lib/bootstrap-stage3/authority.shs` hashes every regular file
under `src/compiler_rust`, pruning only directories named `target`. Compiler
execution creates files below `src/compiler_rust/compiler/build/simple-core/`
and crash reporting creates
`src/compiler_rust/compiler/.simple/logs/crash_*.log`. These are outputs, not
seed inputs. Retained timestamps prove they appeared while the authority build
was active, but do not prove canonical Cargo itself created them; concurrent
test runners were still reachable during the failed attempts. Regardless of
producer, admitting generated outputs into the authority input fingerprint is
the owner defect.

The generated core-runtime directory contained 21 files. Two crash logs were
also retained. Both source-tree output locations were moved into the evidence
directory above so no generated binary or crash log is left as a frozen input.

## Fix and focused evidence

All three fingerprint scans—symlink rejection, regular-file hashing, and Cargo
manifest discovery—now prune only the exact generated roots
`src/compiler_rust/compiler/build` and
`src/compiler_rust/compiler/.simple`. Nested vendored `build` or `.simple`
directories remain fingerprint-sensitive. The existing authority self-test now
proves:

1. Rust/Cargo/runtime source changes alter the fingerprint;
2. files created below `build` or `.simple` do not alter it;
3. symlink and out-of-checkout dependency rejection remains unchanged.

The focused authority self-test passed once: status 0, 9.63s, maximum RSS
79,872 KiB. Evidence:
`build/native_probe/stage4-owner-20260815/authority-fingerprint-generated-output-fix.{log,status,time}`.

The earlier broad `-name target` exclusion remains unchanged and is tracked as
a separate latent provenance defect; it is not part of this already-green
bounded root fix. Next, refresh the frozen manifest for the two attributable
script/test changes and run one cache-preserving
`--full-bootstrap --stop-after-stage2` transaction.

Provider token usage and comparable completed-bug average: unavailable.
