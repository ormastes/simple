# P3 WA: optional tuple payload with Array slot (`WA-P3-opt-tuple-array`)

"unsupported optional tuple payload element type: slot 0 is Array" at the `.0`/`.1` access of
`rt_io_udp_recv_from -> ([u8], text)?` (emitter: src/compiler/50.mir/_MirLoweringExpr/result_tuple_payload.spl).
Optional-tuple lowering supports scalar slots only.

Real fix: extend optional-tuple slot lowering to pointer+len (array) slots. Extern ABI unchanged.

WA site: src/lib/nogc_async_mut/io/driver.spl (_OP_UDP_RECV) — narrow to a typed `([u8], text)` pair
after the nil check, then slot-access the pair. Unverified until the stage3 rerun.
