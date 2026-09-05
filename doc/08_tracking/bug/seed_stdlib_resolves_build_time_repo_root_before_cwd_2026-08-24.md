# Seed resolves `use std.*` from its BUILD-TIME repo root before the process cwd

- **Filed:** 2026-08-24
- **Status:** OPEN (seed fix not landed; the SPL-doctest lane is worked around — see "Workaround landed")
- **Severity:** high — silently compiles a DIFFERENT worktree's stdlib, so fixes
  in the tree under test are invisible and unrelated defects in a foreign tree
  are reported as failures of this tree.

## Symptom

An SPL-doctest block that lives in worktree A is compiled against the stdlib of
worktree B. Concretely, on 2026-08-24 the whole-suite class map attributed 9
doctest failures to `error: semantic: unknown extern function: rt_test_it`. The
`rt_test_it` extern had ALREADY been removed in the worktree under test; the
error came from a **different** worktree's copy of the same file.

The failure mode is worse than a wrong answer: an edit to `src/lib/**` in the
tree you are running from has **no observable effect**, so a correct fix reads
as a failed fix. That is how this sat undiagnosed.

## Root cause

`src/compiler_rust/compiler/src/pipeline/module_loader.rs:2522-2530`:

```rust
let manifest_root = Path::new(env!("CARGO_MANIFEST_DIR"));
let repo_root = manifest_root.join("..").join("..").join("..");
for fallback_root in [
    repo_root,                                        // <- BUILD-TIME absolute path
    manifest_root.join("..").join(".."),
    manifest_root.join(".."),
    manifest_root.to_path_buf(),
    std::env::current_dir().unwrap_or_else(|_| PathBuf::from(".")),   // <- cwd, LAST
] {
    if let Some(resolved) = resolve_from_stdlib_root(&fallback_root, parts, use_stmt) {
        return Some(resolved);
    }
}
```

`env!("CARGO_MANIFEST_DIR")` is expanded at **compile time of the seed binary**,
so it is a hardcoded absolute path to whatever worktree the seed was built in.
It is tried **first**; the process cwd is tried **last**.

This fallback list is only reached when the preceding walk-up (climb up to 10
levels from the source file's directory looking for a stdlib root, stopping at
`is_workspace_boundary`) finds nothing. So the defect is latent for a source
file inside a repo, and fires for any source file compiled from **outside** one
— which is exactly what the doctest lane did by writing its composite to
`$TMPDIR`.

## Evidence (strace, 2026-08-24)

Composite written to `/mnt/data/tmp/...`, run with cwd
`/mnt/data/worktrees/lane-doctest-extern`, binary built in
`/mnt/data/worktrees/seed-deploy-1`:

```
openat(AT_FDCWD, "/mnt/data/worktrees/seed-deploy-1/src/lib/nogc_sync_mut/spec/decorators.spl", O_RDONLY|O_CLOEXEC) = 4
openat(AT_FDCWD, "/mnt/data/worktrees/seed-deploy-1/src/lib/nogc_async_mut/spec/decorators.spl", O_RDONLY|O_CLOEXEC) = 4
```

The tree under test was never consulted for `std.nogc_sync_mut.spec.decorators`.

Direct A/B on the same binary, same source file, changing only where the
composite is written (`TMPDIR` inside the worktree makes the walk-up succeed):

```
composite in /mnt/data/tmp   -> Line 40: error: semantic: unknown extern function: rt_test_it
composite inside the repo    -> Line 40: spec failure: 1 of 1 example(s) failed (exit 1)
```

Same binary, same sources, same command. Only the composite's directory
differed. The first reason was a stale foreign tree's; the second is this
tree's real result.

## Proposed seed fix (NOT landed)

Reorder the fallback array so the process cwd is tried **first** and the
build-time roots last. `resolve_from_stdlib_root` returns `Some` only when the
root actually contains the module, so an invocation genuinely outside any repo
still falls through to the baked root and nothing regresses; the reorder only
changes which root wins when **both** contain the module, and in that case the
build-time path is never the intended answer at runtime.

Not landed here because it requires rebuilding and redeploying the seed, which
this lane does not own. A pure-Simple workaround (below) removes the exposure
for the doctest lane specifically; the seed defect remains open because it
affects **any** compilation whose source sits outside a repo.

## Workaround landed 2026-08-24

`src/lib/nogc_sync_mut/test_runner/doctest_runner.spl` now writes the same-file
doctest composite to `.simple/doctest/` (gitignored, inside the repo under
test) instead of `$TMPDIR`, so the walk-up finds the correct `src/lib`. Names
are slugged per source file so concurrent runs cannot clobber each other.

`src/` was deliberately NOT used as the composite directory: a stray composite
left behind by a killed run would be picked up as a source file by the next
doctest discovery sweep.

## Related

- `doc/08_tracking/bug/unregistered_extern_silent_nil_2026-08-01.md` — the
  `rt_test_it` extern itself had no runtime backing anywhere; fixed separately
  in the same change by routing the spec decorators through the `it` builtin.
