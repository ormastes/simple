# HIR lowering does not register function-local `extern fn` declarations

- Found: 2026-10-20, Stage 2 r16b (self-hosted compiler), while fixing
  bootstrap_main_closure_pulls_src_os_hir_failures_2026_10_20.
- Symptom: `HIR lowering error ... unresolved name: <extern>` for a name that is
  declared by an `extern fn` indented inside a function/method body. The seed
  accepts the same source.
- Minimal repro:

```
fn peek(addr: u64) -> u32:
    extern fn mmio_read32(addr: u64) -> u32
    mmio_read32(addr)
```

  Real sites (all fixed in source by hoisting to module level, the idiom used by
  every other `src/os` file): `src/os/services/netstack/_NetstackService/ipc_handlers.spl`
  (`mmio_read8/16/32/64`), `src/os/services/wm/wm_codec.spl`,
  `src/os/services/wm/wm_service_protocol.spl`,
  `src/os/userlib/_Window/client_methods.spl`,
  `src/os/userlib/_Window/ipc_helpers.spl` (`unsafe_addr_of`).
- Expected: either register the nested extern in the enclosing scope, or reject
  it with a parse/resolve diagnostic in the seed as well, so seed and
  self-hosted agree.
- Status: open (compiler side). Source workaround applied; not a compiler fix.
