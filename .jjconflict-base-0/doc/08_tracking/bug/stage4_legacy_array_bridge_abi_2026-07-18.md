# Stage4 legacy bridges returned incompatible arrays

## Symptom

`runtime_native` used legacy `spl_array_*` constructors in `rt_bytes_from_raw`
and delegated `rt_strsplit` to `spl_str_split`. Those helpers build the legacy
`SplValue` array layout, while pure-Simple Stage4 callers consume canonical
tagged `RtCoreArray` values. `rt_bytes_from_raw` is reachable from LLVM object
emission, so archive section projection cannot make the mismatch safe.

## Fix and prevention

Both bridges now construct canonical arrays through the existing
`rt_byte_array_new_len`, `rt_array_new`, `rt_array_push`, and `rt_string_new`
owners. The focused runtime C test covers byte values `0`, `127`, and `255`, a
null source, empty split fields, no-match splitting, and an empty delimiter.

Raw `runtime_legacy_core.o` remains forbidden as a Stage4 candidate: it still
exports no-op dictionary operations and other bridge-only legacy layouts. A
future compatibility capsule must expose only audited raw-string/platform
helpers and reject legacy array, dictionary, and split exports.

No Simple, compiler, runtime, C, Rust, Cargo, or native execution is claimed in
this static-only session.
