================================================================================
EXTERN FUNCTION FIX - QUICK REFERENCE
================================================================================

PROBLEM: Extern functions throw "undefined function" error
ROOT CAUSE: Not registered in function table
FIX: Add func_table_register() call (ONE line per location)

================================================================================
LOCATION 1: src/compiler_core/interpreter/eval.spl
LINE: 1769 (inside eval_module function)
================================================================================

BEFORE:
-------
        if tag == DECL_EXTERN_FN:
            func_register_return_type(d_node.name, d_node.ret_type)

AFTER:
------
        if tag == DECL_EXTERN_FN:
            func_table_register(d_node.name, did)
            func_register_return_type(d_node.name, d_node.ret_type)

================================================================================
LOCATION 2: src/compiler_core/interpreter/module_loader.spl
LINE: 215 (inside register_module_functions function)
================================================================================

BEFORE:
-------
        if tag == DECL_EXTERN_FN:
            val name = decl_get_name(did)
            val ret_type = decl_get_ret_type(did)
            func_register_return_type(name, ret_type)

AFTER:
------
        if tag == DECL_EXTERN_FN:
            val name = decl_get_name(did)
            val ret_type = decl_get_ret_type(did)
            func_table_register(name, did)
            func_register_return_type(name, ret_type)

================================================================================
VERIFICATION
================================================================================

After applying fix:

1. Build: bin/simple build
2. Test: bin/simple test

Expected: 0 regressions, 300+ new tests passing

================================================================================
UNLOCKS
================================================================================

✅ 33+ runtime functions (rt_file_*, rt_process_*, rt_time_*)
✅ FFI libraries (CUDA, Torch, compression, crypto, regex, SQLite)
✅ Package management system
✅ External integrations (MCP servers, databases)
✅ System programming (mmap, file locks, process spawn)

================================================================================
