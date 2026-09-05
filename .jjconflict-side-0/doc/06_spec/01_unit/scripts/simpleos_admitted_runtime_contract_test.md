# SimpleOS Admitted Runtime Contract

Source: `test/01_unit/scripts/simpleos_admitted_runtime_contract_test.shs`

Evidence class: `host-fixture` plus `source-contract`.

The test constructs a native mock runtime and bound admission evidence, accepts
the canonical fixture, and rejects a signal-139 candidate, a shell-script
candidate, path/hash substitution, an unrelated runtime snapshot, and a newly
forged receipt for unrelated executable evidence. It also checks that build and
scalar-metadata consumers invoke the canonical admitted-runtime verifier and
use compiled validators rather than raw-source execution.

The mock demonstrates verifier behavior only. It is not an admitted production
Simple compiler, a bootstrap receipt, or live SimpleOS execution evidence.

