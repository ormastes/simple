# Dictionary snapshot physical backend checkpoint

Source-only physical helpers, not an activated transaction. Four LLVM IR/status scenarios are authored UNRUN. No native/compiler jobs launched.

C owner header asserts DictSnapshot64 and ArraySnapshot40 with actual offsets. Backend compiler-private storage uses LLVM alloca align8 or Cranelift stack_slot/stack_addr, and C pointer operands to observe/new/fill_publish/dispose. Compiler helper records contain backend value handles, never Simple objects passed as native structs or authority witnesses.

Native fill_publish returns the canonical array handle only from its actual successful fill branch. Both fill and dispose mark consumed, so consumed alone and witness.array loads are not publication. Disposal status remains explicit; lock/cost refusal requires actual scope-owner abort and cannot be called successful disposal or retried forever.

The proposed private snapshot unit dispatcher explicitly refuses until the actual lexical confinement/account/abort owner exists. Helpers are not called by accepted production dispatch. Closed bound→reserve→status CFG, transaction witness lifetime, exact retained input identity, canonical Array<V> metadata reuse and ordinary indexed Struct decode remain planner/caller integration obligations. No i64-to-Array cast, surrogate Struct, raw value reboxing or SOURCE receipt is introduced.

Cranelift helper source uses existing actual stack/call APIs, but generated objects have not been executed. Native wrapper/source assertions and backend helper semantics require independent exact review. No complete snapshot feature or SOURCE availability claim.

Portability correction: C64 layout assertions are guarded and private fill_publish refuses non64 without invoking fill, preserving ordinary32 runtime builds. Cranelift stack alignment argument is exponent3 (8bytes), not8 (256bytes). These uninstalled Cranelift helpers are explicitly host64-only because existing runtime imports use host calling convention; no cross-target route is installed. Future activation must verify actual host ABI or use target-aware imports. Authored tests compare IR/arguments only; they neither assemble LLVM nor execute Cranelift. All remain UNRUN.
