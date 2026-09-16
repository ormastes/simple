# `is_dir` answers false for every real path inside an interpreter-fallback module (and for any backslash path even under JIT)

- Date: 2026-09-02
- Status: OPEN
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
