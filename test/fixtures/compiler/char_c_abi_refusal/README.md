# Direct primitive Char C ABI refusal fixtures

All three fixtures are UNRUN. Use only the existing admitted compiler/native-fixture workflow under separate root authorization. No new runner is supplied.

Each fixture must fail with the exact `E-CHAR-FOREIGN-ABI` diagnostic before its `CHAR-ABI-REFUSAL-MISSING` sentinel. A generic failure, parse/import error, missing runtime or arbitrary nonzero status is not success. `direct_mapping.spl` calls the shared mapper; the other two call actual C/C++ header emitters with a selected direct Char parameter. Existing `test/01_unit/compiler/backend/c_abi_type_mapping_spec.spl` is the positive regression target.

This only covers direct Char reaching the common mapper. Nested pointer/callback/nominal paths, LLVM/JIT ABI, primitive storage and actual C calls remain separate gates. These fixtures do not qualify the future physical UTF8 carrier.
