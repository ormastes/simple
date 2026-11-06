# Parser private state owner APIs

Hand-maintained companion to `test/01_unit/compiler/parser_private_state_owners_spec.spl`.
Execution pending qualified CLI; no PASS claimed.

The registration scenario checks both dictionary fields through the actual
snapshot API, then checks reset clears both. The promotion scenario installs
six nonempty metadata arrays, calls the owner promotion function, and checks
its return value and all six retained values through the snapshot API.
Both scenarios restore the saved state. This checks state preservation, not
allocation lifetime after transient scope teardown; the latter remains a
full runtime qualification requirement. Native planner before/after compilation
also exercises the original cross-module boundary without exposing globals.
