# Native entry closure drops from-import declarations

Status: source defect identified and corrected; native validation UNRUN.

Ubuntu Phase 4 interpreter compilation from frozen source
`43f626850b6a5531e89110f75cd1eaedc24adcd1` with pure Phase 2 producer
`e58968bba401407bb04d6b581e62cf1dcf480847ec56338bb7a06ad4003283ff`
failed HIR with missing module surfaces `core`, `parser`, `ast_convert` and
unresolved `tree_to_module` / `tree_to_expression`. The functions exist and
are exported in `src/app/interpreter/ast_convert.spl`; this is not an absent API.

Evidence directory:
`D:/dev/ubuntu-release-43f626-recovery-20261003/phase34-direct-attempt2/phase4/phase4/llvm/binary/e0154a171690e9eeeb0838eeef7866fe25bb0bd1e7b0a833b56bf594be5df531/`.
Compile exit 1, elapsed 48.45 seconds, peak 651508 KiB, guard completed and
quiescent. The first stderr diagnostics name all three missing surfaces.

The flat parser supports `from M import {names}` in
`src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl` and emits
`decl_use_import`. However, the native entry closure scanner in
`src/compiler/80.driver/driver_source_loading.spl` rejects lines starting with
`from ` in its allocation-saving predicate and lacks a from-import branch in
its dependency extraction. Both paths must accept the declaration. This
change extracts M and passes it through the existing path validation and
source resolution; it does not rewrite interpreter imports or fabricate exports.

The unit spec `test/01_unit/compiler/bootstrap/entry_closure_from_import_spec.spl`
checks the actual interpreter spellings, relative/qualified paths, multiline
lists, exclusions and mixed declaration order. The small native fixture at
`test/fixtures/bootstrap_builder/from_import_closure/main.spl` requires both
a bare sibling and explicit relative dependency, then checks computed output.

Validation requires a source-authoritative producer containing this scanner
fix, not simply compiling the fixture with the unchanged e589 binary. Run the
unit spec on an admitted full runner, then compile/execute the native fixture
with no stub fallback and a phase/producer/closure-bound cache. Require exit
zero and `FROM_IMPORT_CLOSURE_NATIVE_PASS`, then retry the original interpreter
entry. Other errors may emerge after its missing dependencies enter the closure.
No native job has been launched; root retains resource admission ownership.
