# Native function-field callback behavior still incorrect

Status: FAIL, producer-bound native behavioral evidence. Do not mark closure/callback behavior PASS from MIR construction or successful linking.

Producer: c27cb117978d2212cae16a6d956690e13003435f73f2047f1fa237f2fa8a8466, frozen source 6ec114562, Cranelift, one-binary, one compile thread. Runtime capsule: /mnt/wsl/simple-dbc-native-bootstrap-20261012/phase2-runtime-capsules/c27cb117978d2212cae16a6d956690e13003435f73f2047f1fa237f2fa8a8466. Source fixture SHA-256: 0ec089b5b14d0977a25578f8406a98e6fc9f3dbf9252934b35c8f8dfbb627b4e. Rust bootstrap delegation explicitly disabled.

The producer passed bootstrap sanity and receiver checks; general CLI/test qualification remains pending. `check-native-captured-record-callback.shs` compiled and linked the fixture, executed it, then failed exact stdout comparison (status 1). stderr was empty. Expected: opfn_a 11, opfn_b 12, tagfn port, loop_callback 20, each on its own line. Actual: opfn_a 11, opfn_b 12, tagfn 98141896813521, loop_callback 0. The printed integer is this execution's observation, not a stable expected address.

Evidence: /mnt/wsl/simple-dbc-captured-record-c27-evidence-20261012/{compile.log,actual.txt,expected.txt,stderr.txt,inputs.sha256}; checker log /mnt/c/Temp/dbc-captured-record-c27-verification-20261012.log. Compilation no longer fails with E-MIR-EXPR-Lambda, but runtime callback semantics are unqualified. Inspect declared function-field return representation, text tagging, record-return indirect-call ABI and captured-lambda invocation independently; no root cause is proven by output alone. Retain the captured offset and record label assertions. Do not weaken the fixture, accept integer text output, or replace the callback with an integer-only/noncapturing function.

The scoped callback verification budget is exhausted after the parse correction, old-producer closure-conversion failure and rebuilt-producer behavioral failure. No immediate retry or further full bootstrap loop is authorized by this evidence. Report this remaining failure before any further callback verification cycle.

## Source-only candidate, unverified

The method-field redispatch synthesized an untyped `Field` with Unit type.
The indirect-call path consequently selected I64 for every callback result.
Even a typed function callee lowered its entire Function type instead of its
declared return type. It also omitted result HIR provenance needed to read
returned record fields. These source paths account for loss of text formatting
and record result typing; they do not prove the captured-record runtime ABI.

The candidate recovers field HIR type from the selected registered layout,
extracts the Function return for indirect-call signatures, and remembers the
returned HIR type and exact registered record layout. Closure dispatch and
capture storage remain intact. Authored MIR regressions require non-I64 callback
return signatures for text and record callbacks. They are NOT_RUN; behavioral
FAIL remains authoritative and no further verification attempt was made.

Primary review retained the final closure-lift guard as an unqualified patch, not an integrated repair: /mnt/c/Temp/dbc-unqualified-lambda-return-guard-candidate-20261012.patch, based on043d83f4a. It selects concrete Int/Bool/Str/record returns and rejects any lowered-result/signature mismatch, while preserving flat arguments/hidden captures. Unit/float and other valid return paths lack compatibility evidence; broad rejection could regress callers. HIR lambda and constructor expressions also lack contextual function-return typing in some paths. The source diagnostic budget is exhausted, with no new execution or bootstrap. Future bounded qualification must cover ordinary integer, unit, float, text and captured record callbacks, plus actual caller/provider signatures. Existing native FAIL is unchanged.
