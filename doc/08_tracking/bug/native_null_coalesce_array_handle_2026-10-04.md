# Native coalescing loses array representation

Status: repair drafted; compiler rebuild and repaired native execution pending.

An LLVM-produced Windows compiler built from
`ad5d9865e8469c141a61786899990c378cf20abf` compiles the production argv
facade's `val runtime_args = rt_cli_get_args() ?? []` with an integer
conversion followed by text-length dispatch. The resulting native program
crashes with Windows access violation `0xc0000005`.

The compiler executable SHA-256 is
`84c36744623a49a91f1bb108ad987431719ea5a61969ea42ed5f1e18993b5ff3`.
COFF relocations in the reduced `get_args` function identify
`rt_value_as_int_wide` followed by `rt_string_len`. Debugger capture places
the failing caller at that text-length call. Adding `[text]` to the local
declaration avoids the text-length crash but still produces an invalid array
handle and no usable argv. The annotation is not a complete repair.

The MIR coalescing branch defaults an unannotated expression to `i64`.
Array type recovery must happen before decoding either branch. The merged
result must also retain array and element-type metadata. Runtime registry
checks must remain intact; accepting unregistered pointers would conceal
the compiler defect and introduce unsafe dereferences.

The native regression source is
`test/fixtures/compiler/native_coalesce_array_handle.spl`. It covers external
argv, a present optional text array, a missing optional array with a default,
array indexing, and lazy default evaluation. Run its compiled executable with
an additional argument and require exit zero plus exactly
`PASS coalesced native arrays` on stdout. The diagnostic native-build source
collector currently excludes the fixture directory; copy the unchanged
fixture to an isolated build-source directory before compiling it.

The proposed repair preserves declared array/slice types through coalescing
and records their type on the merged local. It has not yet passed execution
with a rebuilt compiler. Existing Phase 3 runs use frozen older source and
must not be counted as validation of this change. No release qualification
or full-suite pass is claimed.
