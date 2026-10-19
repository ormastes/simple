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
