# Planner admission portable hashing

Executable source: `test/02_integration/compiler/bootstrap_planner_portable_hash_spec.spl`.
Requirement: REQ-PLANNER-PORTABLE-HASH-001.
Status: manually reviewed scenario document; SPipe regeneration and native
SSpec execution pending a qualified full CLI.

1. Run the isolated production-helper fixture with only `shasum` available.
   Verify successful completion, empty stderr, and the fixture verdict. Its
   assertions compare known hashes and exact multi-file snapshot records.
2. Invoke the production text helper with a provider that prints a valid
   digest but exits 1. Verify exit 1 and no emitted digest or stderr.
3. Hash empty input through the production text helper. Verify exit 0,
   empty stderr, and the exact standard empty-input SHA-256 digest.

The shell fixture has passed independently. This document does not claim
that the SSpec runner executed these scenarios or that a bootstrap completed.
