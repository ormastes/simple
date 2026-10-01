# Mixed incremental-object link failure blocks focused compiler tests

Status: OPEN / test-infrastructure blocker.

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
