# Generic enum method receiver loses its applied type

Status: source repair prepared; executable verification pending. This does not
admit a compiler or qualify the running frozen bootstrap campaign.

## Observed failure

The `89d2e18cd1487a1f3c5b2c248f9096b3df6b4b0a` frozen Stage 2 matrix
reports `generic enum pattern requires concrete declaration-ordered type
arguments` for `src/lib/nogc_async_mut/failsafe/core.spl` while building the
full CLI. The first fatal is at line 158452 of
`/tmp/phase3-stage2fix-89d2/canonical-admission/stage2-compiler-tests/aarch64-unknown-linux-gnu/verification/logs/compiler_cli_build.log`.
The fixture's original `FailSafeResult<T>` methods match `self` directly.

## Cause and scoped repair

Two boundaries discard generic owner information:

1. `parse_enum_decl` creates an unparameterized synthetic impl for inline
   methods. Preserve the enum's declaration-ordered binders and construct its
   applied target only at this known synthetic-impl construction site.
2. The parser has already typed a method receiver as a bare owner. HIR supplied
   the enclosing impl's receiver context only to untyped parameters. Supply
   that context to the first nonstatic `self`/`me` parameter, and adopt it only
   when the parsed receiver is the same nominal owner without arguments.

This ports the enum-parser portion of `73789ebee82` and the receiver repair
`3bab7052592`; neither was present on the inspected target `c345d0a6e58`.
Other changes from those branches are excluded. Explicit annotations of other
types and already applied receiver types remain authoritative. Explicit bare
generic impls retain the existing missing-arguments diagnostic; no enum
payload validation is relaxed and no failsafe library workaround is added.

## Regression and evidence boundary

`test/01_unit/compiler/mono/generic_class_impl_template_lowering_spec.spl`
covers parser binder ordering, the original `unwrap_or`/`is_ok` shapes,
actual HIR method receiver owner and parameter-symbol identity, reversed
payload order, an explicitly annotated different receiver, and missing
arguments on an explicit bare impl. Existing opaque explicit-head behavior is
preserved rather than claiming generic specialization support.

`git diff --check` passed before the final evidence update. Compiler execution
is deferred because the live campaign was reported above 44 GiB against its
48 GiB cap. No Rust seed fallback, full bootstrap, or frozen-source mutation
was performed. Runtime, performance, and memory improvements are unverified.
