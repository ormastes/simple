# macOS named-type lowering reads transient custom-primitive registry arrays

Priority: P1. Status: source fix implemented; native verification blocked.
Parent row: `macos_native_struct_roundtrip_double_to_ptr_2026_09_21`.

## Evidence

Audited from `17883250f21`, on macOS arm64. The three-file
`test/fixtures/macos_struct_roundtrip/main.spl` reconstructs the recorded
ResultValue argument/return round-trip. The admitted Stage2 binary SHA-256
`e1c0f79a7f0bc9b42df99b1219293e9c3852742a24843e07f96e81d5dcbcd81a`
segfaulted during MIR lowering of `result_code`, before the historical LLVM
`double to ptr` error. The newer Phase2 snapshot SHA-256
`9aea8349b6fb411e46b325ecff70d2924173533d4c2e71d41e2619e9998c41a1`
stalled while lowering `round_trip` until its 100-second process-group limit.
A one-second macOS `sample` placed all 639 thread samples in
`custom_primitive_underlying_type_tag_by_symbol` or its array lookup callees.
Footprint was 408.7 MB. No executable was produced.

`reset_all_pools` assigns fresh custom-primitive names, symbol IDs, and type-tag
arrays during parsing. Streaming parse/HIR scopes end before MIR named-type
lowering consults `custom_primitive_underlying_type_tag_by_symbol`. The driver
promoted aspect/effect/criticality/layer registries but omitted these arrays.
Even an empty registry therefore left stale array headers. This establishes a
missing ownership promotion and is consistent with the sample; the original
LLVM conversion failure is not yet proven resolved.

## Change and regression

`custom_primitive_promote_transient_owner` promotes all three owners, including
dynamic names. The existing driver registry promotion gate calls it while the
scope is paused and propagates failure before teardown. Parser scratch pools
retain their existing reset behavior.

`test/fixtures/custom_primitive_transient_owner/main.spl` checks populated,
empty, and replaced registries across three native scopes, missing symbol/name
lookups, and rejection when promotion is called outside a paused scope. Compile
it with the admitted Stage2 bare positional `native-build` route and
`--backend llvm --runtime-bundle core-c-bootstrap`; run the executable and
require exit 0 plus `custom-primitive-transient-owner-ok`.

The focused compilation using the admitted binary above also segfaulted in
MIR before an executable was emitted. It imports source containing the repair,
but the compiler itself predates that repair. Three bounded native attempts
exhausted this session's iteration cap. Rebuild Stage2 with the fix, execute
both fixtures, then run the required compiler/lib/MCP checks and Stage3 gate.
These remain pending; do not close the original bug or claim verification PASS.

Local logs: `build/struct_roundtrip_probe/{before,snapshot,owner}.log` and
`build/struct_roundtrip_probe/sample.txt` in the isolated worktree.
