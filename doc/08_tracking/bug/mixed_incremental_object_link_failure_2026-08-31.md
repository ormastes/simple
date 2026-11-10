# Mixed incremental-object link failure blocks focused compiler tests

Status: OPEN / test-infrastructure blocker. (Re-verified BLOCKED 2026-11-11, lane
ne15: the formerly blocked artifact is now in-tree, but the doc's required
fresh-target cargo validation cannot run without a cargo grant. See addendum.)

## Evidence

The single bounded 300-second attempt to run the focused JIT symbol-trace
unit did not reach its assertion.  It failed at the Rust test-binary link step
with `rust-lld: error: undefined hidden symbol` errors referencing multiple
`simple_compiler-0758242ea9cfaef2.*.rcgu.o` incremental object variants.

Receipt:
`build/native_probe/phase3-sffi-symbol-trace/receipt-300s.txt`

```text
status=101
SHA-256(test-300s.out)=
6642bb812981ec3dc69c85e6e012497d54b2cd3aff2dca03365329ed7dc347b4
```

The existing 570 MB test binary predates the pending source change; newer
object files were present in the same debug target cache.  The link evidence
therefore indicates incompatible/mixed incremental objects, not a failure of
the new trace assertion or JIT symbol resolution.

## Required validation

Validate the exact focused command in a **fresh, isolated Cargo target
directory** (for example a new `CARGO_TARGET_DIR`), preserving the existing
cache for forensic comparison:

```text
cargo test -p simple-compiler --lib \
  codegen::jit::tests::symbol_trace_groups_private_helper_and_module_qualified_near_match \
  -- --exact --nocapture
```

Only a test-binary link and assertion pass from that fresh target can validate
the pending opt-in JIT diagnostic.  Do not delete or overwrite the current
incremental cache to make the failure disappear.

## Impact

The opt-in `SIMPLE_JIT_SYMBOL_TRACE` diagnostic remains unverified and must
not be committed or used to authorize a Phase3 candidate until the isolated
focused test executes and passes.


## Addendum 2026-11-11 (lane ne15) — BLOCKED on cargo; formerly blocked artifact is now in-tree

Facts established this pass (worktree simple-p3-ne15-20261111, tip
f7640d20a458, fresh seed 46fe8f6b6def):

- The pending opt-in diagnostic landed: `emit_unresolved_symbol_trace` at
  `src/compiler_rust/compiler/src/codegen/jit.rs:523`, gated by
  `SIMPLE_JIT_SYMBOL_TRACE` (`jit.rs:666-667`).
- The exact focused test named in this doc exists in-tree:
  `symbol_trace_groups_private_helper_and_module_qualified_near_match` at
  `src/compiler_rust/compiler/src/codegen/jit_tests.rs:81`, under `mod tests`
  (`jit.rs:834`) — i.e. the doc's `codegen::jit::tests::...` path.
- The environmental precondition (mixed incremental objects under
  `build/native_probe/`) cannot exist in this worktree: it is a fresh
  checkout, `build/` is untracked, and `build/native_probe/` does not exist.

**Not run** (lane constraint — no cargo/rustc): the doc's required validation.

**Exact grant command requested** (run from the repo root of this worktree):

```sh
CARGO_TARGET_DIR=$PWD/build/p3-ne15/cargo-fresh \
  cargo test -p simple-compiler --lib \
  codegen::jit::tests::symbol_trace_groups_private_helper_and_module_qualified_near_match \
  -- --exact --nocapture
```

Expected on grant: test-binary link + assertion pass (the diagnostic and test
are in-tree; the fresh target dir removes the mixed-incremental precondition).
Status stays OPEN until that command executes and passes.
