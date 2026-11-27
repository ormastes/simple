# Executable evidence and traceability contract

This is a design note, not a generated SSpec manual. Documentation-only source
acquisition cannot be marked PASS for algorithm conformance or 99% coverage.

The user's target is at least 99% measured branch coverage for the identified
production algorithms, separately by implementation/backend/target. Register
all loaded-file branch sites, including zero-hit branches. Report covered and
total branch counts, source revision, binary SHA-256, target, backend, command,
exit result and coverage artifact SHA-256. UNMEASURED is neither zero nor 100%.
Keep decision/condition/branch metrics distinct. Disclose unreachable branches
and reasons without silently removing them. Reference C/Rust oracle coverage
and vendored code are not Simple production coverage.

For every requirement in the adjacent tables, the owning worker records an
existing or new exact test path/scenario and source anchor. A test filename alone
does not establish satisfaction. Track states SOURCE_ACQUIRED, AUTHORED_UNRUN,
EXECUTED_PASS, EXECUTED_FAIL or BLOCKED explicitly. Gaps remain visible.

Use modern `step("Load the published vector")`,
`step("Hash through the production API")`,
`step("Compare the expected digest")` in primary hash scenarios. These statements
label real loading, production calls and full-byte assertions. Do not introduce
legacy Given/When/Then helpers or no-op steps that pretend to perform work.
If required helper bodies are missing, fail closed until implemented. Reusable
setup/checkers may be hidden/folded in generated manuals; the primary flow stays
visible. Unit tests cover branch boundaries; integration tests exercise real
callers/streaming/persistence where present; system scenarios explain behavior.

Independent expected bytes must come from the pinned upstream vector corpus or
a separately recorded compatible reference invocation. Store input length,
input bytes/generation rule, seed/secret/key/context, expected full digest and
oracle source revision. Self-generated goldens from the production owner are
not an independent oracle. Compare byte arrays or complete canonical encodings;
prefix matching and inequality-only collision tests cannot prove correctness.

Typed byte/protocol evidence must call the fail-closed comparator; capture alone
is observation. Parse failure, missing fields and empty selections fail rather
than becoming empty successful comparisons. Generated manuals bind spec and
artifact hashes. Run admitted self-hosted `spipe-docgen` and require zero stubs;
if no admitted runner exists, retain AUTHORED_UNRUN and do not hand-write a
generated PASS. Executable `_spec.spl` files remain under `test/`, mirrored
manuals under `doc/06_spec/`. Bootstrap is stopped and seed fallback forbidden
for this campaign.

Final review must inspect actual production owners, assertions, oracle provenance,
modern manual quality and denominator evidence. Source review by Astra is owed
before the root integration owner lands these documents with implementation.
