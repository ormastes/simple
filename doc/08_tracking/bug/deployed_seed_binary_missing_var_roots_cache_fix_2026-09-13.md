# Deployed seed binary predates `VAR_ROOTS_CACHE`; `variants/__init__.spl` opened 76x per lint run

- Status: OPEN (2026-09-13) -- fix already landed in source, needs a redeploy
- Area: compiler / seed module resolution (deployed binary vs source drift)
- Found by: lane PERF-8 (loader/resolver startup perf), attributing the
  `variants/__init__.spl` 76-open pattern PERF-5 handed to L3
- Binary: the deployed seed `bin/release/aarch64-unknown-linux-gnu/simple`,
  sha256 `3d120a6f9ab5704b2225654e4f2773cdbdc787108bd21b67aab657ffe3da72ef`
  (same binary PERF-2, PERF-5 and L3 all pinned), aarch64

## What

`simple lint <2-line file>` (`SIMPLE_EXECUTION_MODE=interpret`; the default
lane segfaults here, see
`lint_default_lane_segfault_from_worktree_bin_path_2026-09-13.md`) opens
`variants/__init__.spl` **76 times** in one process. gdb breakpoints on the
real glibc open functions (`__libc_open64`, `__GI___open64_nocancel`),
printing a backtrace on every match, show all 76 come through:

```
fs::read_to_string
  simple_compiler::module_resolver::var_overlay::compute_var_roots
  simple_compiler::interpreter::interpreter_module::path_resolution::resolve_module_path_uncached
```

Disassembling `compute_var_roots` in the DEPLOYED binary
(`gdb -batch -ex "disassemble 0xc10e70,+400"`) shows it is fully inlined with
`compute_var_roots_uncached` -- function entry goes straight to
`Path::join("variants")`, a `path_kind` check, then (if the dir exists)
`Path::join("config/var.sdn")` + `read_to_string::inner`, then another
`Path::join("__init__.spl")` + another `read_to_string::inner`. **There is no
thread-local `HashMap` lookup anywhere in the disassembly** -- no cache check
at all.

But the CURRENT SOURCE, at this worktree's base `d522cc98da2` (and in every
worktree checked out from `origin/main` at or after that commit), already has
the fix:

```rust
// src/compiler_rust/compiler/src/module_resolver/var_overlay.rs
thread_local! {
    static VAR_ROOTS_CACHE: RefCell<HashMap<PathBuf, Vec<PathBuf>>> = ...
}
pub(crate) fn compute_var_roots(project_root: &Path) -> Vec<PathBuf> {
    if let Some(hit) = VAR_ROOTS_CACHE.with(|c| c.borrow().get(project_root).cloned()) {
        return hit;
    }
    ...
}
```

`git merge-base --is-ancestor 8533c416681 d522cc98da2` -> `YES`. Commit
`8533c416681` ("lane rebuilt as one commit on origin/main") and its
predecessors `7bb5ef796a6`/`07b1cf5221c` are already on `origin/main`. This is
the same fix landed by lane L3 (`ef9ecf31420` in L3's own worktree,
`RECEIPT_L3.md`), which was explicit that its candidate binary
(`simple.l3`) needed a redeploy for the fix to take effect and that
"the new spec is RED under the deployed seed until a redeploy" -- but that
warning did not prevent PERF-2 and PERF-5 from independently re-measuring
the SAME stale symptom on the SAME stale deployed binary and (correctly, at
the time) attributing it to L3's *unmerged* claim rather than realizing the
merge had since landed and only the binary was behind.

## Why this is not "fix the resolver" work for this lane

There is no source change to make here. The memo already exists, is already
tested (`var_roots_are_computed_once_per_project_root`,
`memo_is_keyed_by_project_root_not_shared_across_projects`,
`a_project_without_a_variants_dir_has_no_roots` -- all three still present
and passing in `var_overlay.rs`'s own `#[cfg(test)] mod tests`), and is
already on `origin/main`. **Redeploying the seed from current source is the
only action this needs.**

## Repro (this worktree's private binary; do not extrapolate to the shared clone without checking its binary's sha256 first)

```sh
sha256sum bin/release/aarch64-unknown-linux-gnu/simple.perf8   # 3d120a6f9ab5704b...
gdb -q -batch -ex 'disassemble simple_compiler::module_resolver::var_overlay::compute_var_roots,+400' \
    bin/release/aarch64-unknown-linux-gnu/simple.perf8
# -> no thread-local / HashMap instructions; straight to Path::join + read_to_string
```

## Confirmed against a clean base build (not just `git merge-base`)

Built a binary from `d522cc98da2` exactly (`simple.perf8base`, sha256
`c460e551...`) to rule out any confound from this lane's own commit:

```
gdb -q -batch -ex "info functions compute_var_roots" simple.perf8base
# 0x...  <LocalKey<RefCell<HashMap<PathBuf, Vec<PathBuf>>>>>::with::<...compute_var_roots::{closure#0}>...
# 0x...  <LocalKey<RefCell<HashMap<PathBuf, Vec<PathBuf>>>>>::with::<...compute_var_roots::{closure#1}>...
# 0x...  simple_compiler::module_resolver::var_overlay::compute_var_roots
```

The thread-local memo closures are present -- direct, binary-level proof the
fix is upstream of `d522cc98da2`, independent of anything this lane touched.
Measured `variants/__init__.spl` opens on `simple lint <2-line file>`
(SIMPLE_EXECUTION_MODE=interpret): deployed seed 76, `simple.perf8base` **1**,
this lane's candidate **1**. `check --help` interpret lane: deployed seed 13,
base **1**, candidate **1**.

## Suggested next step

Whoever owns the next seed redeploy: rebuild
`src/compiler_rust` in release mode and redeploy `bin/simple` as usual; no
code change is needed to close this record, only a note that the redeploy
also fixes this specific 76-open pattern (independently of anything else the
redeploy carries). This lane's own private candidate binary
(`simple-perf-8`'s worktree, built from `d522cc98da2` + this lane's one
`pipeline::module_loader` commit) already exhibits the fixed behaviour --
see `RECEIPT_PERF_8.md` for the measured before/after on that candidate.
