# Item 5 current-source research and design update

This supplements existing optional-provider and executable-size designs.
Status: researched design; implementation and host admission remain unproven.

## Current-source findings

provider_admission/state.spl and admission.spl provide metadata single-flight,
ABI/dependency checks, effect-owner selection and terminal publication. Existing
unit tests mix behavioral state tests with source-token checks. They do not prove
actual native loading. Descriptor authority currently cannot express the full
target/architecture/policy-generation contract.

The pinned capability check compares digests, open state and descriptor but does
not bind its member table/geometry to the validated image/receipt. Check current
archive types before implementing member equality and archive bounds; reject
disagreement before any receipt publication or demand read.

provider_call_boundary_v1.spl admits signatures but explicitly does not dispatch.
Reuse src/os/smf/provider_loader.spl for real artifact/query/callable-address and
pin/lifetime admission. Metadata admission and runtime loading need an explicit
binding of artifact identity, target, ABI, policy and ownership; an ABI digest
alone is not target evidence. Do not introduce another independent native loader.

runtime_feature_closure.spl is absent in current source. Historical BS1 completion
text therefore needs a current implementation/evidence inventory. Exact roots,
maps and dependency products must be derived from the actual production link.
Linux runtime_sqlite_demand.c is a family-specific prerequisite, not proof for
all providers or Windows. Optional CLI imports/calls and raw source fallback
must be removed through admitted command providers, preserving every feature.

## External design constraints

GNU ld documents that --as-needed is evaluated at the library's position in the
link; dependency exclusion must inspect final DT_NEEDED and exact input order,
not assert that a flag appeared. Section GC follows roots and relocations.
See [GNU ld options](https://sourceware.org/binutils/docs/ld/Options.html).

LLVM LTO uses linker-resolved visibility and live symbols. Hidden visibility
and section GC complement an exact dependency closure; neither substitutes for
actual link inspection. See [LLVM LTO design](https://llvm.org/docs/LinkTimeOptimization.html).

Loader handles are reference-counted; RTLD_LOCAL is not a full isolation promise,
and close does not prove immediate unmapping. Pin lifetime acceptance checks
our authority to invoke and close rather than assuming OS unmapping.
See [dlopen](https://www.man7.org/linux/man-pages/man3/dlopen.3.html) and
[POSIX dlclose](https://www.man7.org/linux/man-pages/man3/dlclose.3p.html).

## Evidence architecture

Use the concrete acceptance list in
../../../03_plan/sys_test/item5_provider_size_acceptance_2026-10-02.md.
Fixture builders return artifacts bound to source/toolchain/target/profile hashes;
process observers record exit/output/provider initialization and mapping events;
binary inspectors retain root reasons/sections/symbols/dependencies. Mutations
create separate immutable artifacts. Checkers reject missing, stale, malformed
or synthetic evidence. Unimplemented helpers fail rather than certify success.

## Open execution gate

The main-worktree bin/simple.exe identifies itself as a Rust bootstrap seed;
bin/release is absent. Normal TDD needs an admitted self-hosted binary. No
RED/GREEN, production PASS, release admission or supported-host completion is
claimed by this update.
