# Inherent HIR implementations admitted as trait implementations

Status: source repair; native regression and regenerated compiler UNRUN.

The ec7f0118a19e2703e3b092ac775237cd93491271cca26ca4724259a8aa082019
candidate crashed in `relocate_provider_type+624` during the retained layout
fixture. The caller at `register_native_trait_implementations` return PC
0xa6c390 is its first `implementation.trait_` relocation, immediately after
the `has_trait_` byte test, not a parameter/result relocation.

`HirImpl` declares an explicit desugared `has_trait_: bool` / `trait_: HirType`
pair. `lower_impl` passed the optional payload but omitted the flag. The
retained HIR codec scan found 21 monomorphic implementation records whose flag
is `N`, including 20 absent trait payloads and the real counter trait payload.
The decoder restores `N` as nil in the bool slot; a native nonzero-byte branch
can consequently admit an inherent implementation and dereference no type.

The producer now explicitly copies the parser's `impl_.has_trait_` authority.
No relocation null bypass, inferred trait owner, or weakened admission is added.
The mixed inherent/two-trait-implementation fixture checks ordinary methods
and distinct dynamic results through the same trait parameter.

Retained evidence (local, not checked-in):

- `build/item5-trait-enum-layout-cycle2-20261008/diagnostic/layout-gdb-cycle2/mir-gdb.log`
- `build/review/item5-hir-impl-scan-20261008.py` and `.json`: bounded codec scan,
  per-cache SHA256 and record offsets; no execution or cache mutation.
- `test/04_smoke/native_trait_inherent_registration.spl`: four assertions,
  not yet compiled or run. Full layout regression remains required.
