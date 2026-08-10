// FIXTURE — not compiled. Planted input for
// scripts/check/check-extern-abi-signatures.shs --selftest-only.
// Mirrors the RuntimeFuncSpec shape of
// src/compiler_rust/compiler/src/codegen/runtime_sffi.rs.
pub static SELFTEST_SPECS: &[RuntimeFuncSpec] = &[
    RuntimeFuncSpec::new("rt_selftest_ok_c", &[I64, I64], &[I8]),
    RuntimeFuncSpec::new("rt_selftest_ok_rs", &[I64, I64, I64], &[I64]),
    RuntimeFuncSpec::new("rt_selftest_cstr", &[I64, I64], &[I8]),
    RuntimeFuncSpec::new("rt_selftest_arity", &[I64, I64, I64, I64], &[I64]),
    // Return-type row: result is a RuntimeValue (I64). bad_ret_defs.c returns
    // `const char*` with the SAME arity, so only the return check sees it.
    RuntimeFuncSpec::new("rt_selftest_ret", &[I64, I64], &[I64]),
    // Header-coverage row: definition lives in platform/good_hdr_defs.h.
    RuntimeFuncSpec::new("rt_selftest_hdr", &[I64, I64], &[I8]),
];
