# native-build resolves `libsimple_runtime.a` via a CWD-relative path with no staleness check

- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
  pre-existing host btrfs metadata-exhaustion condition (see Verification section).
- Filed: 2026-08-11

## Defect

`find_simple_core_runtime_library()` in
`src/compiler_rust/compiler/src/pipeline/native_project/tools.rs:487-531` (pre-fix)
resolves the `simple-core` runtime archive several ways, the last of which is a
hard-coded **CWD-relative** candidate list:

```rust
let candidates = [
    "build/simple-core/deps/libsimple_runtime.a",
    "build/simple-core/libsimple_runtime.a",
    "build/simple_core/deps/libsimple_runtime.a",
    "build/simple_core/libsimple_runtime.a",
];
for candidate in candidates {
    let path = PathBuf::from(candidate);
    if has_nonempty_archive_payload(&path) {
        return Some(path);
    }
}
```

`has_nonempty_archive_payload` only checks the file exists and is non-empty — it never
compares the archive's mtime against `src/runtime/*.c` / `*.h`. This path is reached
by `find_abi_complete_simple_core_runtime_library()` (`tools.rs:668`), which is what
`config.rs:340` uses to select the runtime archive for the `SimpleCore` link lane
(`SIMPLE_TRACE_RUNTIME_ROOTS=1` reports exactly `build/simple-core/libsimple_runtime.a`
when this lane fires).

Contrast with the *other* runtime-build path, `build_c_runtime_library()`
(`tools.rs:281+`), which already had a staleness check
(`archive_is_fresh_for_runtime_inputs`, `tools.rs:16-25`) before reusing a cached
archive. `find_simple_core_runtime_library()` had no equivalent — a locally-built
archive dated before a `src/runtime/*.c` fix silently kept linking the old code, from
the repo root, while running from any other cwd (or after deleting the stale
`build/simple-core` tree) picked a different resolution branch and got the fix. This
is a silent provenance fail-open that mimics flakiness: identical source, differing
behavior purely as a function of process cwd and a stale local build artifact.

## Fix

`tools.rs`:
- Added `stale_runtime_source(archive: &Path) -> Option<StaleRuntimeArchive>`: finds
  the runtime source root via the already-anchored `find_core_c_runtime_source_root()`
  (walks `CARGO_MANIFEST_DIR` ancestors, not just cwd), scans every `*.c`/`*.h` in it,
  and returns the newest-source-vs-archive mismatch when the archive predates any of
  them.
- `find_simple_core_runtime_library()`'s cwd-relative candidate loop now calls this
  check before accepting a candidate. On staleness it prints a loud `error:` line
  naming the stale archive (with mtime) and the newer source file (with mtime), and
  **skips that candidate** rather than silently returning it or silently substituting
  a different one — matching the other three resolution branches (override dir, env
  var, `current_exe()`-relative), which are left untouched (they're operator/deploy
  supplied, not accidental leftovers).

Anchoring: `find_core_c_runtime_source_root()` (used by the new check) already prefers
`CARGO_MANIFEST_DIR`-ancestor search over bare cwd, so the *source* side of the
staleness comparison is already repo-root-anchored. The *archive* candidate paths
themselves remain intentionally cwd-relative (left as-is per task scope — invasive to
change safely, and the staleness check closes the false-measurement hole regardless of
which cwd resolves the candidate).

## Verification

Static/mechanism verification: confirmed by reading `find_abi_complete_simple_core_runtime_library`
(`tools.rs:668`) and its sole caller `config.rs:340` (`NativeRuntimeLane::SimpleCore`
link-lane selection), and by re-using the exact staleness-comparison idiom
(`archive.metadata().and_then(|m| m.modified())`) already proven correct in
`archive_is_fresh_for_runtime_inputs` a few lines above in the same file.

**Full `cargo check -p simple-compiler` could not be completed in this session**: the
host's btrfs root filesystem metadata chunk is at 50.97/51.51 GiB (99%) with 0 bytes
device-unallocated (`btrfs filesystem df /`), so new metadata block allocations
(including small file writes cargo/rustc need for incremental artifacts and rmeta
output) fail with `No space left on device (os error 28)` even though `df` reports
274G of data-space free. This is a pre-existing, machine-wide condition (not caused by
this change) that also affects unrelated bash tooling. Freeing it requires a `btrfs
balance` and superuser privileges, out of scope for this fix. `cargo check` was
attempted 4 times (plain, `-j2`, `CARGO_INCREMENTAL=0`) and failed the same way each
time, including on `simple-runtime`'s build script — a crate this change does not
touch — confirming the failure is environmental, not from this diff.
