# Windows native runtime hash disagreement

Status: OPEN. Independent of the repaired pure-Simple public hash alias link.

The focused Cranelift native executable built with the frozen bootstrap seed
and LLVM 23.1.1 MSVC tools returned these values for `hello`:

- `std.hash.rt_hash_text`: -6615550055289275125.
- `std.nogc_sync_mut.src.hash.rt_hash_text`: -6615550055289275125.
- Foreign `extern fn rt_hash_text(text) -> i64`: 538079189680823091.

The two pure-Simple values match known FNV-1a. The foreign comparison failed
with an assertion violation. Cross-language parity is FAIL in this diagnostic;
the cause (including text representation at the ABI boundary) is unconfirmed.
Do not infer a production runtime result from this bootstrap repair probe.

Local evidence is `C:/dev/simple-windows-hash-link-fix/build/native_probe/`:
`hash-alias.LiaUB8/results.log` preserves the initial assertion failure;
`hash-alias.lFLsT4/results.log` preserves all three observed values.
The final narrowed link probe checks six pure-Simple alias assertions only:
empty and hello known values through each public alias, alias agreement for
hellp, and discrimination between hello and hellp. It does not gate parity.

Run `scripts/check/check-native-hash-public-alias.shs PRODUCER RUNTIME` for the
narrow link probe. Full cross-language parity remains required separately.
