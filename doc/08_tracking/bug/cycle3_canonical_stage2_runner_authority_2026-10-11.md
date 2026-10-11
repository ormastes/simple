# Cycle 3 canonical Stage 2 runner authority

Cycle 2 c2a88e77 compiled 1,229 units without failure and passed Hello, but its
manual constructor did not capture the canonical prebuild tuple or publish
Stage 2 admission. Those facts cannot be retrofitted. Three native semantic
repairs must be reviewed before freezing the upcoming Cycle 3 source HEAD.

`scripts/bootstrap/run-release-stage2-qualified.shs SOURCE_ROOT EXPECTED_HEAD
FRESH_OUTPUT [JOBS]` is an executable entry into the existing canonical trust
root lane. It validates a clean exact source HEAD and fresh output, then runs
`--full-bootstrap --stop-after-stage2 --mode=dynload --backend=cranelift`.
The wrapper is POSIX shell and is invoked with `sh`. It also sets
`SIMPLE_NO_BOOTSTRAP_DELEGATE=1` to suppress ordinary CLI fallback. The Rust
native constructor does not read that flag; the canonical constructor owns
its explicit transcribed environment. `--strategy=full` selects the full
Stage 2 matrix; normal would select the slim profile and omit MCP/LSP work.
The canonical owner captures source/runtime/tool snapshots and argv before
construction, runs genuine bootstrap sanity and struct-receiver evidence,
publishes immutable Stage 2 admission, builds phase-bound CLI/test-runner tools
and executes phase verification. In the reviewed canonical source, the phase
matrix runs at lines 4871-4883, the real evidence publisher/failure gate at
4884-4908, and the stop-after-stage2 exit occurs afterward at 4921-4928.
It stops before Phase 3/4. Delegated seed
tests are explicitly disabled; failure to execute in-process tests remains a
failure. No ordinary seed test command or fabricated receipt is introduced.

This route cannot preserve the external C22 seed and capsule used by Cycle 2.
The canonical wrapper selects/rebuilds its source-derived Rust authority; it
does not expose an external seed/runtime override. The wrapper announces this
consequence before starting. A C22-preserving adapter would require sharing
the internal sanity owner and adapting authority selection, with additional
source review; extracting internal functions ad hoc is not authorized evidence.

Fresh ordinary `simple-bootstrap-sanity-evidence-v1` is supported. The
admission writer's composed-input validator returns success for ordinary
schema; archived LLVM composition is not mandatory and binds a historical
argv digest that must not be reused for Cycle 3. The canonical writer and
verifier remain unchanged and use their actual 21-argument tuple.

Validation for this wrapper: shell syntax and diff whitespace only. No
constructor, sanity, receiver, Simple tests or release admission ran during
authoring. Cycle 3 runtime feasibility remains pending, including the known
Phase 2 in-process std.spec barrier. Phase 4 self-hosting remains separately
required, and no release PASS is claimed.
