# Module-loader symbol identity regression

Source: `test/01_unit/compiler/loader/module_loader_mangle_owner_spec.spl`.
Status: three authored scenarios, **execution UNRUN**. This is an authored
companion, not a generated test receipt.

The regression imports the real module loader and real TypeInfo constructors.
It checks that an empty type list preserves the base symbol, concrete types
appear in the instantiated name, and argument order produces distinct names.
It does not copy the compatibility helpers or simulate successful JIT loading.

The intent commit precedes the replacement of calls to helpers absent from the
real owner's import. The two JIT size expressions receive equivalent intrinsic
operations; actual JIT allocation, execution and lifecycle verification remain
separate unrun requirements. See
`doc/08_tracking/bug/module_loader_compat_helper_import_gap_2026-10-04.md`.

Run only with a qualified self-hosted native test route, preserve scenario
verdicts and a failing harness control, and do not treat compilation or exit0 as
proof that these examples executed. The current generated-entry admission gap
is recorded in the item4 linker execution gate.
