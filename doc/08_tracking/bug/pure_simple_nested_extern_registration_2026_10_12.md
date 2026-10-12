# Pure-Simple nested extern registration

Status: temporary workaround verified; authoritative bug DB reconciliation pending.

Bug ID: `pure_simple_nested_extern_registration_2026_10_12`.

The retained Phase2 producer `f2ce31b4e4dea1ea6ca3e8726cd411144914c24ffcf58722021f38c4b6393dec` rejects `ParallelConfig.default_config` in `src/compiler/00.common/parallel.spl`: its nested `extern fn rt_cpu_count()` is parsed, but the following call fails HIR lowering with unresolved name `rt_cpu_count`. The original failed module is retained as the reproducer; its failure was not rerun.

Moving the identical extern declaration to module scope preserves the call, return type, configuration values and runtime symbol. The private candidate produced a real 4,565-byte AMD64 COFF object, SHA256 `a10e1845962f32c10360747236f0362c8215963a563fc59050a6d01be4c23a84`. `llvm-nm` confirms an actual undefined external `rt_cpu_count` relocation; the test did not replace the CPU count with a constant.

Evidence: `build/native_probe/parallel-nested-extern-20261012-astra/`; patch SHA256 `603e82db1a39ea20f2403ef556b5fe207d566d9ae54de0c005fdae96b40418b3`; successful receipt SHA256 `b0f9f6296552fef76672fe4ac61405d9c1cf6001cb3a9591a07c197f892e5d26`.

Recovery reference: `50c8c89f6e476d1e0f3e7b2e1512e7db57a6bd06`, original nested declaration in the same source owner. Workaround commit: pending local commit; append the actual hash after committing.

Permanent repair must register nested extern declarations at their intended lexical scope in pure-Simple HIR lowering. Check the Rust seed for the same behavior. Add prevention cases for nested extern calls in static methods and ordinary functions, identical declarations in separate scopes, and conflicting signatures. Before removal, apply the permanent repair, verify the original nested reproducer and these scope cases, then restore only this tagged declaration move. Fetching a purported repair alone does not authorize recovery.

This object check does not qualify runtime CPU discovery, linking, compiler-wide behavior, memory/performance, or full Phase3. No native codegen behavior changed in the workaround; its scope remains declaration registration only.
