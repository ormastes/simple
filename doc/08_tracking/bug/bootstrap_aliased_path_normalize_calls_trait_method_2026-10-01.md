# Native import alias loses owner and calls an unrelated trait method

Status: focused compiler regressions pass; corrected executable verification pending.

Windows Phase2 source 9e89f101c5028d67e9796b7333a64762625be0c5 compiled
1089 modules and linked c5203b45498d18caab9568a59a19516380973fff33a9292918a82afa1e01fb2d,
but its first p2_add HIR worker failed with 0xC0000005 before claiming a module.
The canonical attempt4 source and output remain untouched.

## Diagnostic evidence

An exact copy of that PE, running against a private checkout of the same
source 9e89 under CDB, reaches the source-authority acquire path using a valid
default policy handoff. The strict direct-worker reproduction leaves both
SIMPLE_SCV_FREEZE_FALLBACK and SIMPLE_SCV_SNAPSHOT_ROOT unset. It faults at
RVA 0x2afb86, dereferencing a null HirType receiver, exactly as the earlier
fallback diagnostic did. This isolates the worker fault without weakening
snapshot validation; it is still diagnostic evidence, not bootstrap admission.

Byte matching against the preserved production COFF objects identifies:

- b0aa6f5c52b92615.o `.text+0x15a6`: AssocTypeResolver.normalize.
- c59a4988b223acda.o: compiler_source_authority_inventory_roots_v1 calls
  compiler__traits__associated_types__AssocTypeResolver_dot_normalize.
- Authored call: normalize_source_selector(relative), imported as
  std.nogc_sync_mut.path.{normalize as normalize_source_selector}.

Evidence lives in D:/dev/bootstrap-hir-av-20261001: strict-default-build-debug.log,
worker-strict-av.dmp, strict-av-receipt.json, and fault-object-disassembly.txt.
The earlier fallback-diagnostic-debug.log and worker-av.dmp are retained
separately. The original production object itself proves the wrong callee
binding independently of the diagnostic path.

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

## Focused verification

Windows Cargo verification of frozen c542bd96846a5092008f47493ca0e599ef126a93
passed all three tests selected by `import_alias_` (zero failures), including
both new native-owner and non-native regressions. Logs are retained under
D:/dev/bootstrap-hir-alias-windows-test-20261001/cargo-test.{stdout,stderr}.log.
This is bootstrap compiler evidence, not a self-hosted test-suite pass.

The original attempt4 Rust seed compiled all three fixture modules and its
executable printed -30 twice, proving wrong direct and function-value targets.
Explicit `--no-entry-closure` is required because `--entry` otherwise enables
pruning and can omit the decoy. This baseline uses the known-good 9e89 core-C
runtime as a mixed-runtime diagnostic; its executable, compiler hashes, logs,
and receipt are retained under D:/dev/bootstrap-hir-av-20261001/alias-baseline.
The corrected executable must use the combined current source and print 42
twice before this fix is qualified for another bootstrap attempt.

The private parent cold SCV inventory scan was stopped after the strict
direct-worker reproduction established the fault. Its isolated cache remains
retained; no green acceptance check was rerun.
