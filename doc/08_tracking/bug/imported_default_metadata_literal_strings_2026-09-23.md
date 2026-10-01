# Imported default arguments and literal-string recognition

Baseline: `09837db049777774a61fade41e05895d613fe2ff`.
Status: focused Rust HIR regressions and independent Astra review PASS.
Production coverage-reset native fixture remains pending the combined producer.

## Cause

Imported functions registered return types and names but did not transport
parameter-default AST expressions. A prior attempt to add that transport still
produced one HIR argument for `filters(true)` when the declaration expected
`(enabled, include = "", exclude = "blocked")`.

The remaining bypass is `is_constant_default`: ordinary double-quoted strings
are parsed as `Expr::FString`, including literals without interpolation. The
predicate accepted `Expr::String` but rejected the literal-only FString. The
new parser/HIR regression proves this actual representation before checking
the missing default. `lower_fstring` already turns literal-only parts into a
plain HIR string; accepting exactly those parts does not capture caller state.

## Correction and ownership

Transport default vectors through a module-identity/name map and rebind the
selected exports into the caller even on cached imports. Aliases belong to the
caller map and never overwrite declarations in the source module. Distinct
owners with the same function name retain independent defaults through facades.
Local and flattened declarations use their emitted symbol as the key, including
all-None vectors that authoritatively indicate no defaults. Calls must resolve
to a global free function before defaults can be inserted. Local callable
parameters and named-argument calls retain their existing behavior.

The constant predicate accepts only FString literal parts. Interpolated
defaults remain unfilled under the existing conservative policy. The generic
ABI padding path and runtime string ABI are unchanged.

Direct/group bindings visit only selected names; glob bindings visit the
source contract map once. Local calls use their symbol map without imported
path lookup. Imported path normalization uses the existing path cache. No new
source-tree scan or runtime hot-path I/O is introduced.

## Verification evidence

Worktree: `/Users/ormastes/simple-tmp/imported-default-metadata-20260923`.
Evidence: `build/native_probe/imported-defaults/{red,green}.log` and matching
RSS/terminal receipts. Wrapper: `build/native_probe/run-default-tests.sh`.
Private target is an APFS clone of the previous defaults lane's verification
cache; no shared cache was written. Command uses the locked/offline nightly
Cargo toolchain, pinned LLVM23, target `aarch64-apple-darwin`, package
`simple-compiler`, `--lib imported_default_metadata_tests`, jobs 1, and the
verification-only bootstrap profile overrides opt-level 0, LTO false, codegen
units 256, debug 0. No deployment artifact is admitted from this profile.

Cycle 1: the owner-safe transport was present but the literal predicate still
rejected FString. Six positive tests failed, including direct omitted call
arity 1 versus 3; the local-callable/named-argument negative passed. The literal
test confirmed the parser representation and rejected caller interpolation
before failing its literal insertion assertion. Elapsed 52.02s; sampled peak
3,446,880 KiB.

Cycle 2: literal-only FString accepted; six previously failing tests passed in
30.91s, test execution 0.01s. Sampled peak 3,501,360 KiB. The already-passing
negative was skipped. Cases cover direct/partial/explicit calls, aliases,
reexport chains, local declarations, cached same-name owners, source-alias
pollution, flattened owner symbols, required parameters, and interpolation
exclusion. These assert exact HIR argument counts, types and literal values;
they do not independently prove emitted callee routing or native execution.

Both receipts report zero observer errors, quiescence, and sampled enforcement
at 5,859,375 KiB (`hard_memory_limit=0`). The ordinary 1 GB compilation target
remains unmet. Red versus incremental green compilation is not a runtime
performance comparison; no speedup is claimed. The known rust-objcopy libLLVM
strip warning remains recorded and nonfatal; this change does not fix it.

Green test binary SHA-256:
`ad9d4c9bad4aa79e89c9cc6f3d07e0185ddefec1a2ab156bd083ab9d7ca6604f`.
Working direct-env audit passed; executable-spec layout count is zero.
Independent Astra-high review PASS covers this HIR metadata scope and retained
red/green evidence, with no test reruns by the reviewer.

## Remaining integration gate

`test/fixtures/native/coverage_inventory_global_defaults.spl` imports the real
flat-AST/inventory modules and checks disabled/enabled state, omitted versus
explicit defaults, aliases, exclusions and 1,000 duplicate visits. It was
handed off from the earlier coverage lane and has **not** been built or run.
It requires the independently accepted unit-return fix `bb75cc06519` and Bool
global-inference fix `8521ee4b7cb`, plus a producer rebuilt with this change.
Root owns that combined P0 probe after integration. No full CLI, bootstrap,
production native PASS, compiler-suite PASS, or push is claimed by this lane.
