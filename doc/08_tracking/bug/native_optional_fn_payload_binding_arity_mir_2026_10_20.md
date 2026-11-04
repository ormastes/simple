# `if val f = self.opt_fn_field:` loses the function signature in self-hosted MIR

- Canonical id: native_optional_fn_payload_binding_arity_mir_2026_10_20
- Date: 2026-10-20
- Status: open (workaround active)
- Producer: producer4 strict (source 02ca146 + 81e50f5d441), phase-3 native-build of
  `src/app/cli/bootstrap_main.spl`, x86_64-pc-windows-msvc, llvm.
- Original failure: `dynamic callable requires proven arity before indirect emission` at
  `src/compiler/80.driver/driver_build/parallel.spl:503:45` and `:597:53` (module
  `compiler.driver.driver_build.parallel`, reported 4x incl. worker re-prints). The callee is
  the payload bound by `if val owner_collect = self.owner_collect_fn:` where the field is
  `Option<fn(text, text) -> text>`; the bound local's type reaches the call as `Any`, so the
  indirect call has no proven arity. The Rust seed compiles the same source.
- Workaround: both calls go through `_parallel_owner_collect_call(collect: fn(text, text) -> text, ...)`,
  whose declared parameter type gives the indirect call its signature. Marked
  `# @workaround bug=native_optional_fn_payload_binding_arity_mir_2026_10_20`; recovery
  reference for the original form: `35123ed70c0`.
- Root fix needed: `if val` / Option payload binding in `src/compiler/50.mir` should remember
  the declared inner `Function` type on the bound local (as it does for record payloads).
- DB reconciliation: pending (no qualified `check-dbs` CLI on this host).

## Root cause (2026-10-20, work/p6-mir-misc)

- Not a MIR binding gap first: the flat type parser (`src/compiler/10.frontend/core/parser.spl`,
  explicit `Option<T>` branch) registered a TYPE_OPTION_GENERIC tag only for a named inner
  (`inner >= TYPE_NAMED_BASE`). A callable inner is interned in `TYPE_FUNCTION_BASE..LIMIT`
  (9750..10000), below that bound, so `Option<fn(text) -> i64>` collapsed to bare
  `TYPE_OPTION` = `Option<any>`. Every consumer then saw an `Any` payload. (`fn(..)?` was not
  affected: `parser_absorb_optional_suffix` registers any base.)
- Same class, phase 3 (producer6): `compiler.backend.linker.macho.provider_closure`
  (`if val callback = self.load_v2:` / `self.load`) and
  `compiler.backend.linker.elf.elf_operation_bindings:203` (`self.read_operation.unwrap()`).
- Fix: the parser registers callable inners too; MIR keeps a declared `Function` inner on the
  Option `.unwrap()` result, and an indirect call whose callee is typed `Option<fn>` (the raw
  `if val` binding) calls the payload (`rt_unwrap_or_self`) under the inner signature.
- Status: root fix in review; the parallel.spl workaround stays until a producer built with
  the fix compiles the original form (per bug_linked_workarounds.md).

## 2026-11-04 triage (n88b, opus-n88b): fix already landed, verification-pending

Parser (`10.frontend/core/parser.spl` ~line 1097, callable/composite `Option<T>` inners now keep
their tag) and MIR (`50.mir/mir_lowering_stmts.spl` ~1320-1364, `rt_unwrap_or_self` under the
declared inner signature) are both on release/1.0.0. Seed run: `test/01_unit/compiler/50.mir/phase3_misc_container_callable_lowering_spec.spl`
10/10 pass, including "calls an Option<fn> field through if-val and unwrap with a proven signature".
Stage3 repro: native-build `src/app/cli/bootstrap_main.spl` after reverting `parallel.spl:498`
to the original `self.owner_collect_fn(...)` form; expect no `dynamic callable requires proven arity`.
