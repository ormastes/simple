# Native Result text payload loses its MIR text representation

Status: source repair proposed; native validation with a rebuilt producer pending.

Producer SHA-256: `c978ab12656b7bf67d4bf9b6cc6450d08181c9140b19266863e93b3eba57e5f4`.
Runner SHA-256: `e9b8cf88c24d1f694dd4ad2d6e8b4b2fbe042b4dd60147fdc2d194e943acc8f8`.

The plain private-daemon calibration failed before launching a child. The real
secure temporary directory existed, but `secure_temp_dir(parent, prefix)?` was
concatenated as the decimal value `1819984454161`, so creation of `owner.token`
failed. The API correctly returns `Result<text, text>`.

LLDB disassembly of the actual runner shows `rt_enum_payload` at
`private_session_start_v1 +2090`, then `rt_raw_i64_to_string` at `+2125` on that
same result before string concatenation. Evidence is retained in
`D:/dev/simple-runner-next-evidence-20261030/owned46-private-session-disassembly.log`;
the failed run is `accept-plain-green-1793341429788333600` in the same directory.

`lower_try_expr` routes Result success payloads through
`decode_declared_enum_payload_slot`. Its scalar decoder preserved the i64 carrier
for text and only remembered the HIR type. The MIR concatenation path therefore
treated the carrier as an integer. Both static and recovered Result return types
use this decoder.

The repair restores text through `option_text_value` with `bootstrap_text_type`,
matching existing Result `.unwrap()` and Optional `?` handling. The runtime
`rt_interp_cstr` resolves a registered string handle to its data pointer and
preserves raw C string pointers. This restores the native ABI and MIR type;
it does not change the temporary-directory API or suppress errors.

Regression: `test/fixtures/compiler/native_result_try_text_payload.spl` checks
text equality, length, marker concatenation, and unchanged Err propagation.
The rebuilt producer must compile and execute it, followed by the real private
daemon calibration. A linked runner alone does not establish either result.
