# Imported default constant loses its declaring module on resident MIR lowering

Status: OPEN. Native regression fixtures and compiler repair are not yet run.

## Observed failure

The actual read-only file-view owner probe at source
`f37c7cfae4349736124adc40d0de21dde85adac6` finished MIR with 55 successful
modules and one failed module out of 56. The imported call omitted
`address_space_budget`; the declaration's default was
`FILE_VIEW_DEFAULT_ADDRESS_SPACE_BUDGET_V1`, a real module constant.
The compiler reported `undefined variable FILE_VIEW_DEFAULT_ADDRESS_SPACE_BUDGET_V1`
at `src/lib/common/io/read_only_file_view.spl:49:33`.

Retained raw evidence:
`C:/dev/p4future3/production_owner/cache/diagnostics/native-build-stderr-23044-2.log`.
The genuine pure-Simple compiler SHA256 was
`3c6eafef89dcae8f22db2ff5b4ea831cda494fe19b0dd847f186792f019a2951`,
built from `f04888bdb33f71acc0cd97c38b412b065edc1fe4`.
This is a distinct default-binding defect; it does not reopen or extend the
exhausted three-cycle Future workaround experiment.

## Actual source path

The retained log enters `aot:lower_to_mir:module:start` for the caller.
`driver_pipeline_lowering.spl` takes the resident `lower_module_transient_scoped`
route. It does not take the archived declaration-repository route.

`prescan_one_function_v1` registers provider `[HirParam]` records in
`bootstrap_fn_param_defaults_register`. That registry retains expressions but
no declaring SymbolTable or global declarations. On an omitted trailing
argument, `pad_trailing_default_args` calls `lower_expr` on the unchanged
provider expression while the lowerer owns the consumer's symbols.

The consumer's `register_imported_global_bindings` scans its own HIR bodies,
defaults and constant initializers. The omitted argument is absent from the
consumer HIR body, so its provider-global reference is absent from that demand
scan. A same-spelled consumer symbol must not repair this missing ownership.

The archive route already has `MirHirDefaultBindingFrameV1`, exact provider
declaration checks and `register_provider_global_bindings_with_initializer_policy_v1`.
Its existence does not qualify or repair the resident route used by this binary.

## Regression and repair boundary

`test/fixtures/compiler/imported_default_owner/main.spl` plus `provider.spl`
form the minimal actual two-module test. The caller imports only the function,
omits its default argument, and checks the provider value 37. It also checks
an explicit argument 41 as an independent control. `shadow.spl` instead has
its own `LIMIT = 99` and must still receive 37 from the omitted default.
Each executable closure has two modules and uses no Future or Poll.

The repair must transport actual declaring-owner symbols and bind the real
global storage/initializer policy. Replacing the default with a literal,
passing an explicit production argument, importing a same-spelled caller
constant, or inventing an archive authority is not a compiler fix.

The candidate retains the real prescan provider SymbolTable and global rows,
records each defaulted callable's owner, and rejects conflicting owners for
the same callable lookup key. A direct global Var/NamedVar default is rebound
to an owner-qualified consumer symbol through the existing imported-global
storage implementation. Both sides of the same-module check are canonicalized.
Compound defaults and foreign lexical expressions remain outside this narrow
repair; the archive binder is unchanged.

Imported aliases retain their original declaration name:
`module_import_registration.spl` renames an imported constant symbol from its
lexical alias to `imported_name` while retaining `defining_module`. The
compiler-owner harness covers a provider importing `storage.LIMIT as
LOCAL_LIMIT`, with and without an unrelated caller `LIMIT = 99`.

The new registry roots use the existing generic promotion owner. The actual
C runtime promoter recursively walks dictionary keys/values, array members,
enum payloads and tracked raw aggregate words (`runtime_native.c:2811–2834`).
Its function body is unchanged between f048 and this candidate's e6 base:
4987 characters after newline normalization, SHA256
`3bc92c6787cdfd7972809dfafe4f9cd1ae00389abf2e71e224926b4a23a7ecc9`.
This is source evidence, not a completed lifetime test. The UNRUN harness
constructs actual provider HIR inside a transient scope, promotes the registry,
ends the scope, then reads nested SymbolTable, HirConst and enum payload data
only through the retained registry roots.

A generic identity wrapper around `LIMIT` would retain the same missing
constant ownership. Moving the read into a genuine provider helper may change
which owner lowers the read, but its default-call transport is not validated
here. No generic source workaround is claimed to work without that evidence.

## Planned qualification

No native process has been launched for this bug. Root review must admit the
exact source, launcher, compiler/runtime/tool hashes, and fresh memory budget.
With the current main authority (24 GiB) and compiler-static harness (8 GiB),
an 8 GiB / 4-job default probe requires 49 GiB jointly, including OS 4 GiB and
5 GiB margin; the launcher's outside reservation is 41 GiB.

The unchanged original compiler can establish the minimal negative baseline.
A changed compiler-owner harness or a separately qualified changed producer
is required to test compiler changes; running the unchanged binary on a
patched compiler source tree cannot establish that the repair executes.
No full CLI, broad tests, production-owner qualification, or release PASS is
claimed by these fixtures or this report.
