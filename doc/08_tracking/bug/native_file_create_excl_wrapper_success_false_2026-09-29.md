# Native file create wrapper reports success as false

The Target 6 persisted archive fixture creates a CAS transaction directory but does not publish `batch-v1/CURRENT`. Its `TRANSACTION` creation passes a valid path and a 292-byte manifest to `file_create_excl`. GDB showed the raw `rt_file_create_excl` call returns `1` and creates the file, but the Simple `file_create_excl` wrapper returns the tagged false value `0xb`. The caller then treats publication as failed and aborts the transaction.

Changing the extern declaration from `bool` to `i64` and comparing the raw result with zero did not fix the wrapper: disassembly showed `rt_native_neq(1, 0)` returned a nonzero boolean, but the wrapper's native return conversion selected false for that nonzero value. That attempted change was reverted.

Fix native lowering of boolean returns across a Simple wrapper around a raw FFI function, with a minimal regression showing raw `1` yields Simple `true` and raw `0` yields Simple `false`. A local raw-integer boundary with comparison at the caller can be considered only if it passes the native regression and preserves the public wrapper contract.
