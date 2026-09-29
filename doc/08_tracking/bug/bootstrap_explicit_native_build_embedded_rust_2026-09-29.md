# Bootstrap explicit native builds entered the embedded Rust compiler

## Observed boundary

Frozen source `6772d23f5e2b5bd79c22152780d5183440ac342e` and Phase2 producer
`569203737fe7bdfafd6f52cfe1c1c8d6a30ed17b741217a08c267058e2f8283c`
route ordinary `native-build --source ... --entry ...` through
`bootstrap_main.run_rt_native_build`. Its extern `rt_native_build` is reexported
by `src/compiler_rust/native_all/src/lib.rs` from the Rust compiler. A positional
entry combined with any `--source` also selects this route. The binary's Phase2
lineage does not prove that those compiler requests execute pure Simple.

No tools builds or runtime sanities were launched in the fresh Linux tools lane
after this route was identified. The old native argv is explicitly invalidated
in its external evidence directory.

## Correction on exact main base

Base: `09d340400e02e0b133d244d7969c9a106e8fb017`.

Ordinary explicit entries and project input forms use the existing compiled
native CLI coordinator. Its native argument owner validates options, retains
source-root order, shared output flags and worker counts, and rejects missing or
conflicting entries. The direct one-file positional driver and the guarded exact
Stage3/Stage4 routes retain their existing compiler behavior. Optimization
listing calls the existing pure catalogue owner. The foreign compiler extern
and its dispatcher are removed from the bootstrap entry.

The pure native argument owner already requires an entry; its previous Rust
counterpart silently selecting a default CLI is not retained as an entryless
bootstrap build contract. Duplicate explicit/positional entries now fail with
an owned deterministic error.

The coordinator's cold source inventory now refreshes `src` and `test` together,
matching `compiler_entrypoint_admit_v1`. This does not repair or bypass the
separate repository-root `simple.sdn` policy completeness issue.

## Required evidence

- The focused unit spec and native regression fixture must execute against the
  refreshed source and producer; source review alone is not a test PASS.
- A positive source-bounded native fixture must compile and run, with the actual
  pure driver/coordinator call chain bound to producer/source/runtime identities.
- The first serialized cold tools build must produce a real full-scope inventory
  receipt before warm children run. No hand-written inventory or freshness stamp.
- Caret, DevHub and MCP product/runtime checks remain pending until a refreshed
  producer containing this dispatch correction is built and admitted for the
  diagnostic lane. Editing source cannot alter the existing Phase2 binary.

Tests: `test/01_unit/app/cli/bootstrap_pure_native_build_route_spec.spl` and
`test/fixtures/bootstrap/pure_native_build_route_regression.spl`.
