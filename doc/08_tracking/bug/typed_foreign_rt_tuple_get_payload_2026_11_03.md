# Foreign `rt_tuple_get` declaration preserves typed optional payload

Status: FIXED (P1, scoped typed foreign compiler declaration) — parser, HIR, MIR, and core LLVM owner paths passed the retained compiler-owner continuation and independent actual-linkage review.

## Scoped repair

The foreign `rt_tuple_get` declaration path now preserves its typed optional
payload through the parser, HIR, MIR, and core LLVM compiler owners. The repair
is limited to these compiler consumers and this typed declaration path. It
does not claim that the runtime tuple getter's returned payload is correctly
unboxed for every caller, and it does not close the separate historical JIT
`.get(i)` raw-tagged-word finding.

## Durable fixture and verification

The retained fixture is
`C:/dev/p3new/typed_tuple_consumer_probe_20261103/compiler/main.spl`, SHA-256
`BF561DA166A8AD5D2BA3BAB719DD73AA5FCE236540F1546402FF1C9AF5DE516E`. Its 27
native checks cover parser (6), HIR-if (10), MIR named-variable (4), and LLVM
constant (7) owner paths. A strict continuation linked 34 ordinary runtime C
translation units with 592 retained Simple module objects and two entry/init
glue objects, without recompiling Simple modules. It performed zero Simple
compiler invocations, used no compatibility aliases or permissive link flags,
and retained all 594 objects unchanged. The native run passed all 27 checks in
2.2 seconds (rc 0); link and native process trees were reaped.

Astra independently reviewed the actual owner linkage and returned
`SCOPED_COMPILER_OWNER_PASS` in
`C:/dev/p3new/typed_tuple_consumer_probe_20261103/compiler_runtime_continuation_01/owner_review.sdn`,
SHA-256
`5138950168BA265CEE5DF773A224E2849C0983C7ED0D2F99A910FF90E7D7FB33`. The
retained native result is
`C:/dev/p3new/typed_tuple_consumer_probe_20261103/compiler_runtime_continuation_01/attempt_01/result.sdn`,
SHA-256
`0606DB9D26B976A4449678AF5AFA66CFC87FBF54CDC8DAE15C4CE0736AC172B2`; the
executable SHA-256 is
`8A4310E629207EB65A77C89F8D223A273B540ACDF7FBECE9112753470A2C456C`.

## Explicit exclusions

This result does not qualify the plugin consumer, Cranelift, CLI, Phase 2, or
Phase 3. The plugin consumer has a separate blocked boundary, and the
historical JIT tuple getter issue remains OPEN under its original record. No
runtime getter-wide or cross-backend claim is made.

## In-tree regression artifacts

The byte-identical native fixture is preserved at test/02_integration/compiler/backend/probe_typed_foreign_tuple_owners.spl (SHA-256 BF561DA166A8AD5D2BA3BAB719DD73AA5FCE236540F1546402FF1C9AF5DE516E). Its recorded execution used the isolated artifact path; no additional run is claimed for the copied repository path. The reviewed owner-linkage receipt is preserved at doc/08_tracking/bug/typed_foreign_rt_tuple_get_owner_evidence_2026_11_03.sdn (SHA-256 5138950168BA265CEE5DF773A224E2849C0983C7ED0D2F99A910FF90E7D7FB33).
