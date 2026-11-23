# Qualified enum field-array provenance fails a record-layout gate

Status: OPEN; bug DB reconciliation pending because a qualified full CLI database writer is unavailable during bootstrap. This dated report retains the canonical workaround identity and evidence; no bug DB update is claimed.

Producer: frozen pure-Simple P2 `/tmp/simple-rc-build-20261122/recovery-20261123/phase2-frozen`; live campaign source84ea108. Backend LLVM, aarch64-apple-darwin, v1 ABI, core-c-bootstrap.

Original failure: `array return record element has no unique provider layout: lib.nogc_sync_mut.database.bug.BugTokenReading` in `src/lib/nogc_sync_mut/database/bug.spl`. The type is an enum `Unavailable | Count(BugTokenCount)`, not a record. Go-to-end retains independent modules; this row is FAILED, not an objectless facade PASS.

Isolation: a one-module plain `[Reading.Count(...)]` plus parameter array loop emits its object. Constructing `[usage.input, usage.output]` from enum-typed struct fields and then looping over it reproduces the fatal error with the qualified local enum name. Changing that loop to index reads still fails at projection provenance. A scalar-known-count form emits the object; execution and full target-module verification are tracked below.

Workaround: only `BugDatabase.add_token_usage` counts its four existing scalar readings individually. The public `bug_token_total([BugTokenReading])` API, array values, unavailable semantics, overflow checking and database fields are unchanged. Retirement requires the qualified enum provenance owner fix, native original-form fixture success, and original database module success with the repaired producer; a fetched fix alone does not authorize removal.

Underlying repair owner: agent bugtoken_layout. Suspected boundary: canonical qualified enum names from struct field metadata reach record-layout checks without an exact enum registry alias. Do not strip qualification or guess by bare type name. Add same-basename enum/record negative cases before accepting a canonical registration fix.

Evidence directory: `/tmp/simple-wt-bug-token-layout-20261123/build/bugtoken-layout-probe/`. `enum-fields.log` is the real failing tiny original, `enum-fields-index.log` is the failed index workaround, `enum-fields-scalar.log` is scalar workaround collection. No successful final compiler/link claim follows from an emitted object alone.

Recovery source: original block is available in release source commit8f3405ee95f84ceb259d2bcd1abbe8c24e3e5dfa. Workaround commit SHA will be recorded after verification. Final target compile receipt/object path and execution output remain pending.

## Verification and diagnostic object

The exact configured `nogc_sync_mut` target compiled and linked under the frozen producer with LLVM/v1/core-C, one worker, and canonical enforcement/cleanup. Its columns probe ran and returned11. All59 source function declarations have definitions in the emitted126576-byte object (63global definitions), including `BugDatabase.add_token_usage` and `bug_token_total`.

Object: `/tmp/simple-rc-build-20261122/bugtoken-layout-repair-20261123/bug.spl.o`, SHA256 `ff1234658e89a6545e2dabcb9d4ecb6d8a180617b1e7ca76c2b887117ee0fd33`. Exact source/producer hashes and compile receipt are in adjacent `object.sdn`; original capsule receipt is retained unchanged.

The capsule reports `native-module-cache-witness-v1-invalid|...|ambiguous-resolution-fact`. This object is provisional manual-link evidence only. Do not inject it into the normal admitted cache, reseal the witness or call its existence a compiler PASS. Automatic cache reuse requires a separately verified resolution witness; manual linking requires actual source/ABI compatibility and final executable gates.

Actual public API regression compiled and ran with output `token-receipt-native-ok assertions=16`. It covers all-known sum15, unavailable propagation, overflow rejection, all-unavailable admission, mixed-known rejection without knowledge, mixed admission with knowledge, known zero admission, distinct field order1/2/4/8 and total15, and absence of rows from rejected receipts. The self-running fixture is retained at `test/fixtures/compiler/bug_token_receipt/token_receipt_native.spl`. The exact original failing form is retained separately as `enum_field_array_original.spl`; it is intentionally RED on this frozen producer, not a passing spec.

The underlying MIR owner is NOT fixed. Its removal gate must use a newly built compiler that proves qualified enum provenance without borrowing an unrelated bare-name record layout, rerun the original field-array loop, and include separate modules declaring an enum and a record with the same basename. The original database module must then compile and pass the receipt behavior checks before this narrow workaround is removed. The index-read attempted workaround also failed and is preserved in `enum-fields-index.log`.

Workaround change commit: `053c53f8a4e82b1e9d289e2d198b9efa193c52a9`. Keep this owner bug OPEN until the native retirement gates above pass. The diagnostic object was emitted before this commit from identical source bytes; object source hash remains unchanged.

## Known-zero and assertion controls

A separate actual API regression `token_receipt_known_zero_native.spl` passed7 assertions. It specifically proves that `Count(0)` mixed with three unavailable fields is rejected without knowledge, accepted with knowledge, and stored distinctly as input `0`, output/total `unavailable`. This strengthens the zero-count boundary without rerunning the unchanged16-assertion success program.

One separate negative source variant changed only the first expected sum text from `15` to `16`. It compiled successfully, then exited1 with `panic: assertion failed` under canonical complete/observer0/quiescent1; the success marker was absent. Thus the observed positive program's assertions are active, not an exit-zero-only or optimized-away success.
