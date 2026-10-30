# MIR: `Result<(A, B)?, E>.unwrap()` unsupported (2026-10-25)

Native MIR lowering fails with `unsupported Result unwrap payload type: payload is Optional, not a tuple`
(`50.mir/_MirLoweringExpr/result_tuple_payload.spl`, `result_tuple_rejected_element`) when a
`Result` whose payload is an Optional tuple is unwrapped. Seen in run-27e for
`compiler.driver.cache.bootstrap_library_archive_v1` (`library_archive_current_v1` caller).

Workaround (tagged `@workaround` in source): return a non-optional struct with a `found` flag.
Root fix: admit Optional-of-tuple payloads in `result_try_tuple_payload_type`. Status: open.

release/1.0.0: the gap is the same there. `result_tuple_payload.spl` is byte-identical to base
`d3fc04205cf`, including the `payload is Optional, not a tuple` rejection. The source workaround
is not ported: `src/compiler/80.driver/cache/bootstrap_library_archive_v1.spl` does not exist on
release/1.0.0. Only this record and the in-development spec are carried there.
Review note: the message is built in `result_tuple_payload.spl`, but the gate that rejects it on
release/1.0.0 is `result_optional_inner_supported`
(`50.mir/_MirLoweringExpr/method_calls_literals.spl` ~877, `case _: false` for a Tuple inner,
reached from the `Optional(inner)` arm). The root fix probably belongs there, not in
`result_try_tuple_payload_type`.
