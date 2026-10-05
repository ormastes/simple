# Bootstrap stage2 discovery preprocess rejects nested @when/@else chains

Status: open, 2026-10-05. Lane: work/rendering-skia-harden-20261005
(phase-2 verification side finding; unrelated to that lane's rendering
changes).

## Failure

`bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2
--backend=cranelift --jobs=10 --no-mcp --clean-rebuild` on
origin/main `50f656a675c` (aarch64-apple-darwin, M4, 26 GB):

```
Build failed: failed to preprocess
src/lib/nogc_sync_mut/io/path_identity_abi.spl during discovery:
unsupported @when condition at line 20
```

Line 20 is the `@else:` introducing a nested `@when(os="freebsd"):` chain
(committed in a52c7718fab, 2026-10-03, "feat(linker): forward static
linkers"; also present on release/1.0).

## Why it matters

The same tree BUILDS stage 2 successfully in the default incremental mode
(verified 2026-10-05: 1198 modules rebuilt, stage-2 admission + sanity
passed on `817fef0f97c`, which contains a52c7718fab). So the rejection is
specific to the `--clean-rebuild` / cold-discovery preprocessing path,
which raw-parses `@when` chains the incremental path strips differently.
Same class as
doc/08_tracking/bug/rust_seed_full_scan_os_when_raw_parse_2026-10-02.md.

## Suggested directions

- Teach the discovery preprocessor the `@else:` + nested `@when` form, or
  pre-strip os-guard chains before the discovery raw parse.
- Reproduce minimally: a two-branch `@when(os="linux")/@else/@when(os="freebsd")`
  file through the cold discovery path.

## Evidence

- worktree log: build/bootstrap-lane-20261005.log (clean-rebuild run,
  VERDICT ABORTED stage=stage2)
- contrast run: same command without --clean-rebuild on the same tree
  (renders this doc) — stage 2 outcome pending at writing.
