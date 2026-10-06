# Binary object CAS verifier returned a nilable value as bool

The original static-only LLVM and Cranelift native object specs both reached native emission but failed because binary_object_cas_verify returned nil against its non-optional bool contract. The function returned read(...).? directly. The language quick reference specifies .? returns T?, so an explicit conditional must produce true or false.

The isolated pure-Simple repair preserves bounded no-follow reads, magic checks, digest checks and every original assertion. Both static-only owner cases passed with the pinned Phase 1 snapshot (2/2, zero skipped). The separate CAS owner spec remains 1 passed, 4 failed; a baseline run without the repair has the exact same failures. Those failures concern typed-byte literal values such as 127_u8 being treated as unit, blocking to_i64 and casts. They remain unresolved and are not waived.

Raw evidence: /tmp/simple-object-cas-repair/{static-owner,cas-owner,cas-baseline}.log and corresponding .rss.env receipts, plus compiler.sha256. The child binary is the preserved Phase 1 snapshot. No synthetic producer result was written. Core and native smoke checks, complete Phase 1 qualification and later phases remain pending; this focused result is not a release PASS.

## Fixture follow-up

The four baseline failures were caused by fixtures using the unit suffix `_u8` instead of numeric type suffix `u8`. The lexer explicitly separates numeric suffixes (`u8`, `i64`) from underscore-prefixed user-unit names. Corrected only literal spellings, retaining function names, conversions and assertions. A selected-case harness omits the already-passing malformed-digest case. All four previously failed cases passed (4/4, zero skipped), covering magic recognition, verified publication/deduplication, poisoned authoritative bytes and bounded reads. Raw evidence: /tmp/simple-object-cas-repair/cas-fixture.log and cas-fixture.rss.env. The retained fifth-case pass comes from the earlier owner run; this is combined case evidence, not a fresh whole-file result.
