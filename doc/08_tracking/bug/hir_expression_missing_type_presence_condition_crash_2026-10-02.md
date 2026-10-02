# Synthesized HIR expressions advertise absent type metadata

After the class metadata and LLVM parameter-array fixes, producer `8f817f2b6d5430ab6a18f36e8c9e136857783341adfea8741acfe7a5aea552d4` compiles and runs both ordinary and exported/documented class controls. The original loader closure still exits 139 at a different location: `MirLowering.lower_cond_operand+1050`, reading `cond.type_.kind`.

Bounded GDB payload inspection shows the HIR expression's `has_type_` field is the raw nil sentinel `3`, and `type_` is also `3`. The consumer correctly gates the type read on the presence flag, but the omitted flag was filled with truthy nil by the bootstrap compiler. The retained synthetic condition span maps to pattern matching in the loader source. This is not a class payload or MC/DC instrumentation defect; ordinary conditions use the same lowering helper without coverage enabled.

A comments-aware constructor audit found 76 HIR-lowering constructors with explicit `type_: nil` and no explicit `has_type_`. They now set `has_type_: false` beside the absent payload. Two tuple-element constructors whose payload can be present now set the flag from the same array-bound condition used to obtain that payload. Existing typed constructors are unchanged. The MIR consumer is not modified to mask the invalid producer contract.

`pattern_condition_metadata_native.spl` exercises successful literal-pattern arms and a fallback arm without depending on the separate native assertion ABI bug. Its runner must require exactly `pattern-condition-metadata-ok`. The earlier class control remains a separate, already-passing criterion and need not be repeated unless a new change affects it.

Evidence: pinned source `classfix-source-fcb35f85cd/build/native_probe/class-control-validation/{original-loader,original-loader-debug,condition-payload-debug}`; static consumer disassembly at `D:/dev/linux-mir-crash-20261002/class-after-184d/lower-cond-8f.asm`. GDB's own exit zero is not a compiler PASS. Native validation of the producer repair is pending.
