# Specialization ownership across compiler module aliases

Status: candidate; native regression and repaired compiler qualification pending.

The attempt8 dedicated test-runner build completed HIR for 304 modules, then
failed strict ReturnTypeInterface registration with E-RTI-006: one batch mixed
`compiler.frontend.core.types` and `compiler.core.types`. No runner artifact was
published. This is the ReturnTypeInterface, not runtime type information.

The retained types HIR cache contains the canonical owner and zero occurrences
of `compiler.core.types`. Monomorphization deliberately places specializations
under every logical key for a physical module, but created each new symbol with
that placement key as its declaration owner. Existing original declarations
retain physical source ownership. Thus an alias view could contain original and
specialized function rows attributed to different modules.

The candidate uses the admitted module path for new specialization symbols in
normal, legacy, and scoped placement. Empty-path synthetic modules retain the
existing logical-key fallback. Signature validation receives its existing
module-path argument. Lookup keys, importer resolution, user module names, and
strict mixed-owner RTI rejection remain unchanged.

Coverage adds actual process_modules execution followed by strict RTI row
registration for a canonical and historical key of one numbered source. It
retains both original and specialized functions. A separate filesystem fixture
imports both names and calls a real generic function through each name. These
checks have not yet run on the repaired producer; Astra source review passed with no P0/P1/P2 findings. The typed regression
exercises unbudgeted processing; budgeted and scoped producer execution remain
pending.

Evidence: `/tmp/simple-release-1.0.0-phase2-runner-attempt8-parallel-20261030/stage2-test-runner-build-cwdfix/build.log`.
Retained cache: `cache/hir/f5b4ada266c5109497620c1572f0dd30962b7c8ae833137d699d082f26e87575.parser-v4.hir`
under that build directory. The cache-byte observation localizes introduction
of the alias label; it does not by itself prove the proposed repair at runtime.
