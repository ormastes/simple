# Qualified callable parameter prescan lookup miss

Status: source repair; native qualification pending an authorized producer build.

Compiler16 SHA-256 `1566993a6722fdf0e7546182838da4fbb8064c9c67c2acaa77fd8afe91054ed8` contains the method-Any boxing branch, but the real SSpec positive still fails. Retained LLDB evidence is `/tmp/simple-sspec16-matcher-diagnosis-20261030/evidence.sdn` and `equality.log`: `rt_native_eq` receives boxed 41 (`0x148`) and raw 41 (`0x29`). The produced executable exits 1.

The retained HIR function `to_equal` has scalar receiver and `Any` expected argument. Its relocated callable symbol has no function type and uses the admitted provider-qualified link. Both full-HIR and compact-declaration prescans registered parameter types only under the bare function name. `resolved_call_hir_param_types` queries the relocated qualified name, misses, and returns an empty signature, leaving the method argument unboxed.

The repair registers the same parameter list under the exact `prescan_call_name` computed by its existing owner. It introduces no guessed/sanitized alias and retains the existing symbol-free type admission, nominal rejection, and ambiguity checks. The bare-name registration is unchanged.

The regression in `test/01_unit/compiler/mir/declaration_return_types_v1_spec.spl` calls both production prescan paths with distinct owners sharing a function name: Any, i64, and a provider-local nominal type. It then checks the actual consumer resolver with untyped qualified callable symbols. The nominal provider must not erase the two valid qualified signatures, and neither its exact key nor the rejected bare key may expose foreign SymbolIds.

Source review and whitespace/environment guards do not establish native behavior. The new regression has not yet run against a source-bound compiler. The original SSpec positive remains failed; its negative remains an executed expected assertion failure. No compiler17 build or repeated native acceptance run was launched for this repair. Cumulative six-cycle budget audit remains a prerequisite for another producer cycle.
