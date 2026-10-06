# Binary object CAS verifier returned a nilable value as bool

The original static-only LLVM and Cranelift native object specs both reached native emission but failed because binary_object_cas_verify returned nil against its non-optional bool contract. The function returned read(...).? directly. The language quick reference specifies .? returns T?, so an explicit conditional must produce true or false.

The isolated pure-Simple repair preserves bounded no-follow reads, magic checks, digest checks and every original assertion. Both static-only owner cases passed with the pinned Phase 1 snapshot (2/2, zero skipped). The separate CAS owner spec remains 1 passed, 4 failed; a baseline run without the repair has the exact same failures. Those failures concern typed-byte literal values such as 127_u8 being treated as unit, blocking to_i64 and casts. They remain unresolved and are not waived.

Raw evidence: /tmp/simple-object-cas-repair/{static-owner,cas-owner,cas-baseline}.log and corresponding .rss.env receipts, plus compiler.sha256. The child binary is the preserved Phase 1 snapshot. No synthetic producer result was written. Core and native smoke checks, complete Phase 1 qualification and later phases remain pending; this focused result is not a release PASS.
