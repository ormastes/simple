# RC graph extern calls unbox tagged text before the runtime owner

Canonical ID: `rc_graph_tagged_text_extern_abi_2026_11_15`.
Status: OPEN; the focused compiler regression is authored but unrun. No changed producer
or runtime pass is claimed.

## Source and object evidence

The C runtime ABI in `src/runtime/runtime.h` declares `rt_rc_share`,
`rt_rc_retain`, and `rt_rc_release` as `int8_t(int64_t value)`, and
`rt_rc_count` as `int64_t(int64_t value)`. The Rust runtime SFFI table uses an
`I64` parameter for all four. They consume the tagged one-word RuntimeValue
handle.

The compiler's text extern table did not list these symbols in
`tagged_text_value_arg_indices`. In the actual P2 compiler object inspected
before this repair, calls through this boundary emitted `rt_interp_cstr`,
`rt_strlen`, and `rt_string_new` before the RC call. The C owner consequently
received a newly boxed string value rather than the original handle. The object
inspection did not print an `rt_rc_count` result, so it does not establish the
observed root count or a runtime failure by itself.

The call lowerer also selected tagged-text rows based on a link-name string
without requiring a registry-proven Foreign declaration. The existing callable
registry records Source vs Foreign from actual HIR declarations; this change
uses that origin for the tagged passthrough only. Unknown names and same-name
Source declarations do not gain the runtime ABI.

## Repair and qualification boundary

The compiler registry now classifies exactly the four RC symbols at argument
index zero. The authored focused regression is intended to run production HIR,
MIR and LLVM lowering for text extern, same-name Source and non-text generic
`i64` cases. If run successfully, it checks emitted call shape; it does not
replace changed-producer runtime qualification.

Required next qualification: compile the changed compiler/runtime bundle from
tracked source, inspect the actual emitted object to confirm the RC call receives
the original tagged value without an intervening C-string bridge, then execute
a focused RC share/count/release probe against that changed producer. The old
admitted P2 executable remains baseline evidence and is not fixed by this source
change. Keep the separate kernel-image memo ownership change as an independent
dependency; do not rebox the memo or probe to avoid this ABI repair.
