# LLVM loader returns an optional wrapper as a DynLib receiver

- Canonical ID: `llvm_loader_optional_receiver_2026_11_03`.
- Status: FIXED 2026-11-03 — commit 292fee2b7ee (llvm_lib binds the optional payload); test/01_unit/lib/sffi/llvm_loader_optional_receiver_spec.spl 1/1 passing under bin/simple.exe test.
- Severity: P1, native LLVM provider calls fail after a successful library load.
- Owner: `src/lib/nogc_sync_mut/sffi/llvm_loader.spl`, `llvm_lib`.
- Acceptance: `REQ-LLVM-LOADER-OPTIONAL-RECEIVER`, covered by
  `test/01_unit/lib/sffi/llvm_loader_optional_receiver_spec.spl`.

The accessor promises `DynLib`, but previously copied `_llvm_lib: DynLib?`,
tested presence, and returned the original optional word. In the retained native
failure, `DynLib.load` constructs `Some(lib)` with discriminant1 and type hash
`0xf1987159`. The accessor tests `rt_is_present` and returns that wrapper
unchanged. `DynLib.sym_checked` then reads the wrapper as a DynLib record:
the path field becomes `0xf198715900000001`, and the lifetime identity becomes
the payload pointer. The lifetime owner correctly refuses that unrelated key.

The fix binds the optional payload explicitly with `if val lib = _llvm_lib`.
The missing-provider panic, configured provider selection, lifetime checks,
symbol resolution, and foreign call transport are unchanged. No compiler,
runtime, or provider guard is bypassed.

## Retained failure

The existing producer is `36F452B0CA65D46B5FD6F5457DDADE4F158B85BB2BA5900DE20737CFAB601456`.
The failed native executable is
`7EA8B592A9DF904E1F26C20D7BEDB35CC6A56155BA331278A5D3E4AA24EBD2FE`.
It verified the actual DLL path/hash and process identity, then failed with
`E-SFFI-019: provider mapping is retired` before the plugin19 semantic END.
Neither a real unload nor use-after-free is inferred from this message.

Evidence is retained under
`C:/dev/p3new/typed_tuple_consumer_probe_20261103/attempt_02/plugin_identity_bridge/`:
`result.sdn`, `provider_failure_review.sdn`, and the `option_load`, `lifetime`,
and `resolve` diagnostic disassembly files.

## Independent cause and finite verification boundary

The earlier optional-global lane concerned allocation of a `MirStatic` and
`StoreGlobal` for a None initializer in `_MirLowering/module_lowering.spl`.
Its retained direct probe already had both, but reported Option construction
and runtime-identity diagnostics. Its three recorded attempts and explicit
no-further-attempts boundary remain unchanged.

This accessor cause has one observed native failure and no completed repair
verification. Independent review classified it separately because construction
and global storage succeeded; the error is the accessor's missing payload
binding. At most one focused verification is allowed. No seed, P2, P3, or
bootstrap rebuild is permitted. No admitted self-hosted executable was found
at the repository release path during preparation, so no alternative engine
was used and no runtime PASS is claimed.

The authored regression exercises the actual loader, verifies a stable handle
and lifetime identity, resolves `LLVMContextCreate` through the normal checked
owner, and creates/disposes a real context. It remains unexecuted. Plugin19,
Cranelift, and bootstrap qualification remain pending independently.
