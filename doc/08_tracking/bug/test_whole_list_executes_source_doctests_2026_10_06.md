# Whole-test listing executed source doctests

The Windows `phase1-discovery-focused40` packet ran `test --whole --list --parallel --max-workers=40 --unstable --mode=interpreter --json` on source 6016134cc8be7c90d437368d627046e38b254362 with seed SHA256 15102d32226b3fbead63d3c63e33e99a6f0e9ffcddea06080fb65872445cbafb. It exited 1 after 3158.115 seconds.

The spec path stopped at 2145 missing-cover annotations before reaching its listing branch; these are admission findings, not 2145 executed assertion failures. The source-doctest path ignored `options.list` and executed 487 examples, reporting 315 passes, 168 failures and 4 errors. Those pass counts are not release evidence while the separate SDoctest verdict-integrity defect remains unresolved. Markdown listing executed zero examples.

Repair: return the spec inventory before execution-only cover validation, and add the missing list-only early return to both source-doctest entrypoints. Keep ordinary execution and its coverage admission unchanged. Add poison-example regressions to demonstrate that listing cannot execute assertions or reject the inventory for absent coverage metadata. Native verification remains pending; do not restart the full suite unchanged.
