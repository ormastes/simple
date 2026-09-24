# `load_module_with_imports_internal` re-reads a package `__init__.spl` once per unflattened submodule import
## Closed 2026-09-16 — Status FIXED 2026-09-13; base 29 opens vs candidate 2, cargo tests RED to GREEN

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

- Status: FIXED (2026-09-13)
- Area: compiler / seed pipeline module loader (used by `simple lint`'s static
  analysis pass, and by native/native-build compilation)
- Found by: lane PERF-8 (loader/resolver startup perf), attributing the
  `fix/rules/impl_/__init__.spl` 28-29-open pattern PERF-5 measured but did
  not attribute
- Binary: the deployed seed `bin/release/aarch64-unknown-linux-gnu/simple`,
  sha256 `3d120a6f9ab5704b2225654e4f2773cdbdc787108bd21b67aab657ffe3da72ef`,
  aarch64 (symptom reproduces on any binary built before this fix)

## What

`simple lint <2-line file>` (`SIMPLE_EXECUTION_MODE=interpret`) opens
`src/compiler/90.tools/fix/rules/impl_/__init__.spl` **28-29 times** in one
process, all from the same thread. gdb breakpoints on `__libc_open64` /
`__GI___open64_nocancel`, backtrace on every match:

```
fs::read_to_string
  simple_compiler::pipeline::module_loader::load_module_with_imports_internal
    simple_compiler::pipeline::module_loader::load_module_with_imports_internal  (recursive, once per submodule import)
```

`load_module_with_imports_internal` (`pipeline/module_loader.rs`) has a
`visited: &mut HashSet<PathBuf>` de-dup, but it only fires conditionally:

```rust
let path = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
if flatten_imports && !visited.insert(path.clone()) {
    return Ok(Module { name: None, items: Vec::new() });
}
let mut source = fs::read_to_string(&path)...;
```

At the recursive call site, `flatten_imports` for the CHILD call is
`flatten_this_import = should_flatten_nested_import(use_stmt, &source) ||
single_import_targets_module_file(&use_stmt.target, &resolved)` -- true only
for glob/group imports or an import that targets a module file directly. A
plain member import of a *package* (`use fix.rules.impl_.some_rule`, which
resolves to the package's `__init__.spl`) is neither, so the recursive call
runs with `flatten_imports=false`, the `visited` check is skipped by the
`&&` short-circuit, and execution falls straight to `fs::read_to_string`.
`fix.rules.impl_` is imported by many sibling rule files under
`fix/rules/`, each import re-reading the same package `__init__.spl` from
disk.

## Fix

Added `MODULE_SOURCE_TEXT_CACHE`, a thread-local memo of the CRLF-normalized
raw source text keyed by the already-canonicalized `path`
(`src/compiler_rust/compiler/src/pipeline/module_loader.rs`), consulted via
`read_module_source_text_cached(&path)` unconditionally (regardless of
`flatten_imports`), replacing the direct `fs::read_to_string` +
CRLF-normalize at the top of `load_module_with_imports_internal`. Scope is
deliberately narrow:

* Caches only the RAW TEXT, before the per-call `target_arch` cfg-strip
  (`strip_inactive_cfg_arch_globals`) and the `SIMPLE_BOOTSTRAP` textual
  leniency rewrite, both of which still run on every call against the cached
  text. A process loading the same file for two different `target_arch`
  values (cross-target native builds) still gets a correctly per-arch
  stripped result -- byte-identical to the unfixed behaviour.
* Does NOT cache the parsed `Module` or the capability-validated return
  value. `flatten_imports=false` revisits still parse fresh and return a
  real, non-empty `Module` every call -- verified by
  `unflattened_repeat_import_of_the_same_package_init_reads_disk_once`
  (`#[cfg(test)] mod tests` in the same file), which rewrites the file
  between two unflattened loads of the same path and asserts the SECOND
  load still returns real content (not the flatten-revisit empty `Module`)
  while coming from the pre-rewrite cached text.
* Wired into `clear_module_cache()` / `clear_module_cache_selective()`
  (`module_cache.rs`) via a new `clear_module_source_text_cache()`, mirroring
  `clear_pipeline_dir_listing_cache` right above it in the same file. As of
  this fix the only callers of `clear_module_cache`/`clear_module_cache_selective`
  found (`grep -rn clear_module_cache src/compiler_rust`) are `#[cfg(test)]`
  fixtures within this crate's own test suite -- `mem_trace.rs:557` already
  records that `lint` and `native-build` never reach `clear_module_cache`
  today. So this wiring currently protects the test harness, not a live
  MCP/LSP staleness path; it is still the right boundary for any FUTURE
  long-lived caller (a `Compiler` reused across a multi-file `native-build`,
  an MCP/LSP session) that adopts the existing `clear_module_cache*`
  convention. A short-lived one-shot process (`simple lint <file>`,
  `simple run <file>`) never calls `clear_module_cache`.

## Verified against a clean isolated base build (not just this lane's candidate)

Built `simple.perf8base` from `d522cc98da2` exactly (this fix's two files
reverted via `git checkout d522cc98da2 -- <files>`, built, then `git checkout
HEAD -- <files>` restored, `git status --short` empty). `fix/rules/impl_/__init__.spl`
opens on `simple lint <2-line file>`: base **29** (true, isolated "before" --
proves the 28-29 count is not contaminated by anything else that landed
between `d522cc98da2` and this lane's HEAD), candidate **2**. `.spl` perf pin
RED verdict on base:
```
SPEC FILE VERDICT: ...outcome=ERROR declared>=1 executed=1 passed=0 failed=1
```
`module_resolver` unit-spec suite (11 files, `test/01_unit/compiler/module_resolver/*.spl`):
base and candidate `SPEC FILE VERDICT`/`Results:` lines diff EMPTY (60 total,
57 passed, 3 pre-existing failures on both -- `numbered_last_segment_single_scan_spec.spl`
2 of 3, `type_domain_resolver_spec.spl` 1 of 4).

## Not fixed here (related, same shape, out of scope for this change)

1. `file_might_define_requested_symbol` (`pipeline/module_loader.rs:852`, called
   from two sibling-scanning call sites at `:914` and `:2216`) does its own
   independent, uncached `fs::read_to_string(path)` to probe whether a candidate
   sibling file defines a requested symbol name. This is a SEPARATE uncached
   read of physical module source, not covered by the fix above (its callers do
   not obviously pass an already-canonicalized path, so routing it through
   `MODULE_SOURCE_TEXT_CACHE` as-is would silently never hit and add a dead
   lookup rather than fix anything -- it would need its own canonicalization
   first). Not attributed to a specific measured count in this session; flagged
   for whoever next investigates a residual repeat-open count on this call
   path.

2. **The candidate's residual 2 opens of `fix/rules/impl_/__init__.spl`** (down
   from 29, stable across repeated runs) are a DIFFERENT, cross-lane
   duplication, not this function still leaking. Root cause: TWO INDEPENDENT
   PER-LANE SOURCE CACHES -- this fix's `MODULE_SOURCE_TEXT_CACHE` inside
   `pipeline::module_loader`, and the interpreter's separate cross-lane
   `PARSED_SOURCE_CACHE` (`module_cache::shared_source`) -- neither one
   knows about the other, so a file BOTH lanes reach gets read once per
   lane no matter how well each lane's own cache works. gdb backtraces on
   the two hits:
   ```
   #0 __libc_open64 (".../src/compiler/90.tools/fix/rules/impl_/__init__.spl")
   #13 simple_compiler::pipeline::module_loader::load_module_with_imports_internal
   #14 simple_compiler::pipeline::module_loader::load_module_with_imports_internal (recursive)

   #0 __libc_open64 (".../src/compiler/tools/fix/rules/impl_/__init__.spl")
   #13 simple_compiler::read_trace::rts::<&std::path::Path>
   #14 simple_compiler::interpreter::module_cache::shared_source
   ```
   `src/compiler/tools` happens to be a symlink to `90.tools`, so in THIS
   ONE case the two lanes' independent resolutions also land on two
   different SPELLINGS of the path -- but the symlink is incidental, not
   causal: `simple check --help`'s default lane shows the SAME two-lane
   duplication on 29 files that involve no symlink at all, with the EXACT
   SAME path string opened twice each (`grep | sort | uniq -c` shows count=2
   for one literal string, not two distinct strings), one read via
   `pipeline::module_loader::load_module_with_imports_internal`, the other
   via `hir::lower::import_loader::parsed_imported_module` ->
   `module_cache::shared_source`. Canonicalizing the impl_ spelling would
   not remove this class of duplication; only sharing one cache across the
   two lanes would. Unchanged between base and candidate on `check --help`
   -- pre-existing, outside this fix's reach, not a side effect of it. Same
   class of duplication `PARSED_SOURCE_CACHE`'s own doc comment already
   names for the lowerer/interpreter pair, just extended to a third lane
   (`pipeline::module_loader`) that predates that unification effort.
   Unifying the pipeline lane into the existing cross-lane cache is a larger
   change than this lane's scope.

## Verification

`cargo test -p simple-compiler --lib` (module_loader tests, RED -> GREEN):

RED (`fs::read_to_string` restored at the call site, cache functions present
but unused):
```
thread '...unflattened_repeat_import_of_the_same_package_init_reads_disk_once' panicked:
assertion `left == right` failed: second load must be byte-identical to the first: ...
  left: 2
 right: 1
```

GREEN (fix applied): `pipeline::module_loader::tests::` 39 passed, 0 failed
(includes the three new tests: `module_source_text_is_read_from_disk_once_per_process`,
`module_source_text_cache_is_keyed_by_path_not_shared_across_files`,
`unflattened_repeat_import_of_the_same_package_init_reads_disk_once`).
`module_cache::tests::` 8 passed, 0 failed. `module_resolver::var_overlay::tests::`
3 passed, 0 failed (unaffected by this change; recorded to show no regression
in the neighbouring cache this fix's doc comment compares itself to).

See `RECEIPT_PERF_8.md` for the candidate-binary strace re-measurement.

