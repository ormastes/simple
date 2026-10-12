# Native function-field callback behavior still incorrect

Status: FAIL, producer-bound native behavioral evidence. Do not mark closure/callback behavior PASS from MIR construction or successful linking.

Producer: c27cb117978d2212cae16a6d956690e13003435f73f2047f1fa237f2fa8a8466, frozen source 6ec114562, Cranelift, one-binary, one compile thread. Runtime capsule: /mnt/wsl/simple-dbc-native-bootstrap-20261012/phase2-runtime-capsules/c27cb117978d2212cae16a6d956690e13003435f73f2047f1fa237f2fa8a8466. Source fixture SHA-256: 0ec089b5b14d0977a25578f8406a98e6fc9f3dbf9252934b35c8f8dfbb627b4e. Rust bootstrap delegation explicitly disabled.

The producer passed bootstrap sanity and receiver checks; general CLI/test qualification remains pending. `check-native-captured-record-callback.shs` compiled and linked the fixture, executed it, then failed exact stdout comparison (status 1). stderr was empty. Expected: opfn_a 11, opfn_b 12, tagfn port, loop_callback 20, each on its own line. Actual: opfn_a 11, opfn_b 12, tagfn 98141896813521, loop_callback 0. The printed integer is this execution's observation, not a stable expected address.

Evidence: /mnt/wsl/simple-dbc-captured-record-c27-evidence-20261012/{compile.log,actual.txt,expected.txt,stderr.txt,inputs.sha256}; checker log /mnt/c/Temp/dbc-captured-record-c27-verification-20261012.log. Compilation no longer fails with E-MIR-EXPR-Lambda, but runtime callback semantics are unqualified. Inspect declared function-field return representation, text tagging, record-return indirect-call ABI and captured-lambda invocation independently; no root cause is proven by output alone. Retain the captured offset and record label assertions. Do not weaken the fixture, accept integer text output, or replace the callback with an integer-only/noncapturing function.

The scoped callback verification budget is exhausted after the parse correction, old-producer closure-conversion failure and rebuilt-producer behavioral failure. No immediate retry or further full bootstrap loop is authorized by this evidence. Report this remaining failure before any further callback verification cycle.
