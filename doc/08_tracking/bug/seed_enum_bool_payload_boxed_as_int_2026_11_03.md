# Rust MIR lowering boxes enum bool payloads as integers

Status: OPEN (P1) — native regression failure and source owner identified; no production fix or closure claim.

## Failure and owner

The failing generic optional-tuple native case reaches the `true optional bool
projection` assertion and panics before its 24-check completion marker. The
retained campaign result is
`C:/dev/p3new/tuple_abi_optional_verify_20261103/attempt_01/generic_tuple_24/result.sdn`,
SHA256 `BB024BFBECF813FC1350612EE81BFEF2010F0E95B807EA6E62B314B92A937A3C`;
stderr SHA256 is
`88A745754C75DA0B9BA110E85A75E00F90EDDFC51790C3235B5E89CC0B74131B` and the
observed panic is `tuple ABI probe failed: true optional bool projection`.
The executable SHA256 is
`C0A67AACC8B7BEF7500C67CB12E96EA70B908861F57017E676C05D682BB66523`. This
failed generic case is separate from the guarded optional-reference binding
fix, whose 20-check and 8-check cases pass on the same seed.

The source owner is Rust MIR lowering in
`src/compiler_rust/compiler/src/mir/lower/lowering_expr_call.rs`: the
`needs_box` path includes `BOOL` and then emits `BoxInt`, producing an integer
tagged value for a boolean payload. In the retained native disassembly, the
input is boxed via `rt_value_int` before `rt_array_push`; optional projection
then performs `rt_is_some`, `rt_unwrap_or_self`, and `rt_value_as_bool`. The
runtime boolean decoder accepts the tagged special-boolean representation, so
this input def/use path explains the observed true-value mismatch. It does not
establish a tuple-getter ABI defect or a production fix.

The offline mechanism receipt is
`C:/dev/p3new/tuple_abi_optional_verify_20261103/attempt_01/mechanism_receipt.sdn`,
SHA256 `D5F3077A70BAC048221F7025E2303A88536F0E02EBEC0B5DA5760B2B8490D719`;
the disassembly excerpt SHA256 is
`C87F1A7D0CCC74C1ED10475E7EEFACD7ABD745A563A25DE54AC85FA6C205EEB5`. The
campaign is a focused diagnostic, not Phase 2 or Phase 3 qualification. The
issue remains OPEN pending a narrowly owned source repair and a native
regression that proves the bool payload representation end to end.

Do not close or fold this issue into the guarded optional-binding fix, the
older generic tuple-getter/FFI hypothesis, the existing candidate AV, or
LayoutAttr requalification. Those records retain their separate scopes and
statuses.
