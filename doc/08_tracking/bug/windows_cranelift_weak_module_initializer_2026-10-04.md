# Windows Cranelift module initializers resolve to empty fallback stubs

Status: rebuilt seed native regression passed; compiler bootstrap validation pending.

The Cranelift-produced Phase 2 compiler aborted before parsing with `str.clear`
receiver rejection. A two-module reduction with `pub var numbers: [i64] = []`
compiled successfully but passed receiver `0x0` to `rt_clear`.

The generated owner object contained the correct allocation and global-store
instructions. However, `__module_init_owner` had COFF storage class WeakExternal
(105), with no auxiliary symbol. The linked PDB placed that name at the same
address as `___module_init_owner_stub`, the empty `/ALTERNATENAME` fallback.
Both the startup dispatcher and a direct C call left the global zero.

Changing only that diagnostic object's symbol class to External (2) made both
calls initialize the global and allowed array clear/push/read to succeed with
output `0`, `1`, `7`. This object edit establishes causality; it is not a shipped
fix, producer admission, or substitute for rebuilding the compiler.

The actual fix exports the Cranelift module-init definition strongly on Windows,
matching the existing Windows global-data ownership rule. Other targets retain
preemptible linkage. Runtime receiver validation is unchanged.

Regression coverage: emitted COFF initializer must be a non-weak definition;
`test/fixtures/compiler/native_module_init_globals` exercises imported empty and
populated global arrays, clear, push, and read on a real executable.

Evidence: `windows-restart-20261004/cranelift-tagging-investigation`, including
`imported-run.log`, `inspect-run.log`, and `strong-run.log`.

The actual rebuilt seed (SHA-256
`08781c5f1dd0344715f3301f0b84111d9b7a3a7d712aadc26eacd524f2bb6235`)
compiled both regression modules successfully (2 compiled, 0 cached, 0 failed).
The resulting executable exited zero and printed exactly
`PASS native module global initialization`. Its retained COFF object records
`__module_init_owner` as External (2), confirming the source fix's output.
This does not yet qualify the subsequent full Cranelift-produced compiler.

The emitted-COFF unit regression passed (1 passed, 0 failed, 4266 filtered).
