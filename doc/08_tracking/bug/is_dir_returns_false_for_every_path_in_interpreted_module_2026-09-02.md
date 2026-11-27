# `is_dir` answers false for every real path inside an interpreter-fallback module (and for any backslash path even under JIT)
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- Date: 2026-09-02
- Status: FIXED (2026-11-11, lane interp9) — both defects verified fixed on deployed seed. See addendum below.
- Severity: high (silently disables every `is_dir`-guarded code path)
- Binary: `bin/simple.exe`, md5 `d52d770724a9f8797e98ac7819709ab9`, 16,347,136 bytes, mtime 2026-09-01 17:54
- Platform observed: Windows 11 (x86_64-pc-windows-msvc)

## Measured

Instrumented `src/app/cli/doc_coverage_command.spl` — a module the JIT drops to
the interpreter over an unrelated HIR error — and ran `bin/simple.exe doc-coverage`:

```
DBG mixed=false bslash=false fwd=false root=false
DBG isdir_lib=false walk=8116
```

`mixed` = `is_dir(cwd() + "/src/lib")`, `bslash` = all-backslash form,
`fwd` = fully forward-slash form, `root` = `is_dir(cwd())`. **All four false**,
including the repository root, on a machine where the directory plainly exists —
while `dir_walk` on the *same string* walked 8,116 entries in the same run.

The same calls from an ordinary module that DOES JIT:

```
ISDIR root=true
ISDIR lib=true
ISDIR bslash=false     <-- still wrong
EXISTS root=true
WALK=8116
```

So there are two distinct defects:

1. **Engine-dependent**: inside a module that fell back to the interpreter,
   `is_dir` returns false for every path, the repo root included.
2. **Separator-dependent, on BOTH engines**: `is_dir` returns false for a
   backslash-separated path (`C:\Users\ormas\dev\simple\src\lib`) that is the
   native form `dir_walk` itself emits. `file_exists` on the root is true.

## Impact

Any code that guards a directory walk with `is_dir` silently does nothing. That
is exactly what happened to `doc-coverage`: `discover_source_files` skipped every
scan directory and the command reported "No source files found in <repo>" (exit
1) on a tree `simple stats` counts 16,220 sources in. Fixed there by removing
the guard (`3d2908f9455`), which does not address the underlying defect — the
next `is_dir` caller will hit it.

## Hypothesis (not verified)

Every run of this seed prints, among others:

```
warning: public function `shell` has 4 co-compiled definitions with 2 differing signatures
warning: public function `process_wait` has 3 co-compiled definitions with 2 differing signatures
... [compiler_cross_module_private_symbol_collision]
```

`is_dir` may likewise have several co-compiled definitions, with the interpreter
path resolving to a different one than the JIT path. This was NOT confirmed — it
is recorded as the first thing to check, not as a finding.

## Next steps

1. Census `fn is_dir` definitions across `src/lib/**` and `src/app/io/**` and
   check whether the symbol collides.
2. Decide whether `is_dir` should normalize separators on Windows; `dir_walk`
   and `file_exists` already accept forms `is_dir` rejects, so the three
   disagree today.
3. Grep for `is_dir(` guards in tooling paths — each is a latent silent no-op.

## 2026-11-11 addendum (lane interp9, work/p3-interp9-20261111) — FIXED, both defects verified on seed

Verdict: FIXED (both defects).

- Defect 1 (engine-dependent): `is_dir` in
  `src/lib/nogc_sync_mut/io/dir_ops.spl:87` now forwards to the real
  `rt_dir_exists` extern instead of the `_dir_shell_bool("test -d ...")` shell
  placeholder that made every answer false interpreted (see the in-code comment
  citing `is_dir_always_false_shell_dependency_2026-09-02.md`).
- Defect 2 (separator-dependent): `rt_dir_exists` on the current seed answers
  true for a genuine backslash-separated native path on Windows (verified
  below). `dir_walk` canonicalises its emitted entries with
  `host_path_canonical`, so the two now agree; the raw extern itself
  (`rt_dir_exists` → `rt_is_dir` → `GetFileAttributesA` on Windows,
  `std::path::Path::is_dir` in the seed's `interpreter_extern/file_io.rs`)
  accepts both separator forms.

Verification actually run (seed-smoke, tracked `bin/simple.exe` build-commit
`46fe8f6b6def`, `SIMPLE_LIB=src`, interpreter lane AND default lane; the probe
module dropped to the interpreter with the documented
`compiler_cross_module_private_symbol_collision` jit-fallback on both lanes —
exactly the interpreter-fallback condition this record was filed under):

- `is_dir(cwd())` → true, `is_dir(cwd() + "/src/lib")` → true,
  `file_exists(cwd())` → true, on BOTH lanes.
- `is_dir` on the true native backslash form of the repo root (built with
  `.replace("/", "\u{5C}")` — see the escape caveat below) → true on BOTH
  lanes. The same string answers true at the raw `rt_dir_exists` extern.

Probe-spelling caveat (recorded so the next verifier is not misled): in a
Simple string literal, a backslash before an ordinary letter is consumed as an
escape (`"\src"` collapses to `src`), so the literal `"C:\...\src\lib"` does
NOT survive to the runtime. Build backslash paths with `.replace("/", "\u{5C}")`
or the `host_path_native` facade — otherwise a probe of this defect reproduces
as an apparent `is_dir` false for a path that never contained backslashes.

Guard: `test/01_unit/app/doc_coverage/file_scanner_native_paths_spec.spl`
already pins the native-separator classifier half of this family.

