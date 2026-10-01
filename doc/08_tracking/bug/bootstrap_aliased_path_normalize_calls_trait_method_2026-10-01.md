# Native import alias loses owner and calls an unrelated trait method

Status: source correction and focused regressions; native verification pending.

Windows Phase2 source 9e89f101c5028d67e9796b7333a64762625be0c5 compiled
1089 modules and linked c5203b45498d18caab9568a59a19516380973fff33a9292918a82afa1e01fb2d,
but its first p2_add HIR worker failed with 0xC0000005 before claiming a module.
The canonical attempt4 source and output remain untouched.

## Diagnostic evidence

An exact copy of that PE, running against a private checkout of the same
source 9e89 under CDB, reaches the source-authority acquire path using a valid
default policy handoff and the explicitly diagnostic SCV fallback. It faults
at RVA 0x2afb86, dereferencing a null HirType receiver. This diagnostic fallback
is not bootstrap admission and is not a reproduction of the full canonical
snapshot environment. The normal parent debugger run remains separate.

Byte matching against the preserved production COFF objects identifies:

- b0aa6f5c52b92615.o `.text+0x15a6`: AssocTypeResolver.normalize.
- c59a4988b223acda.o: compiler_source_authority_inventory_roots_v1 calls
  compiler__traits__associated_types__AssocTypeResolver_dot_normalize.
- Authored call: normalize_source_selector(relative), imported as
  std.nogc_sync_mut.path.{normalize as normalize_source_selector}.

Evidence lives in D:/dev/bootstrap-hir-av-20261001: fallback-diagnostic-debug.log,
worker-av.dmp, fault-object-disassembly.txt. The original production object
itself proves the wrong callee binding independently of the diagnostic path.

## Cause and correction

HIR import_alias_symbol resolves an imported alias to its unqualified original
name unless a local declaration shadows that original. Native per-module
imports retain exact owners in a map keyed by the alias. Erasing the alias
therefore loses that owner and lets the later mangler select an unrelated
same-named method or free function.

Preserve the authored alias when the native qualified-import map owns it.
The existing mangler remains responsible for exact symbol ownership and local
precedence. Contexts without that native map retain the original flattened
alias behavior. No global suffix or unresolved-name fallback is widened.

The Rust regression discovers actual import declarations, lowers HIR and MIR,
and checks both direct calls and function-value symbols against unrelated
method/free-function collisions and local shadowing. A separate no-native-map
case protects original-symbol lowering. The executable SPL fixture under
`test/fixtures/aliased_import/colliding_native_owner` must print 42 twice with
stub fallback disabled; source/object assertions alone do not establish that.

The private parent cold SCV inventory run is CPU-heavy before reaching its
worker; it must not be confused with repeated bootstrap verification. Its
cache is isolated and retained, and no green acceptance check is rerun.
