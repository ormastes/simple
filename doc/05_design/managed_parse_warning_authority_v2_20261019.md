# Managed parser V2 authority binding

<!-- codex-architecture -->

Implementation authored against bb989decd74 in an isolated worktree; runtime,
native qualification, SPipe generation and performance checks remain UNRUN.
This closes source-level authority connections within the selected incremental
build requirements. It does not by itself admit Phase 3 or enable publication.

The existing 16-field qualification receipt retains its format. Its
frontend_identity carries a canonical single-line SDN array of nine strings:
domain, actual base frontend identity, complete prior scope digest, feature
digest, capture policy, flat codec version, result wire version, result SDN
version and diagnostic profile. Expected identity and issuer/worker/target pins
come from the trusted caller boundary independently of submitted manifest,
receipt and environment. Admission never supplies missing expected pins from
those inputs.

The parent cache decoder exposes SHA-256 of the exact validated scope substring
after its FPC/codec prefix. This preserves lane, backend, CPU, features,
optimization, compiler/source, provider and optimizer dimensions. Qualification
supports its existing strict parent configuration; unsupported profiles reject.
Fixed versions and the feature hash algorithm live in pure common owners, with
existing frontend entrypoints reexported unchanged. Run admission imports no
frontend parser or CAS implementation.

The cache hash binds canonical frontend identity, worker image digest, OS,
architecture and CPU. `managed_parse_run_admit_v2` validates the whole existing
run, checks independent worker/target pins, exact derived cache equality in
profile/snapshots/bindings/actions, exact transported identity, explicit feature
settings and capture policy, then calls existing qualification admission.
The runner's separately owned `grouped_run_v2` must call this gate before its
internal engine; V1 must reject warning policy and V2 identity inputs. Production
CLI `grouped-run-v2` requires all eleven closed named arguments.

Launch environment contains one case-insensitively unique
`SIMPLE_MANAGED_PARSE_FRONTEND_IDENTITY_V2` assignment. It transports admitted
preimage data, not new trust. The separately owned V2 worker compares actual
local switches/policy and derived cache identity before parsing and per action.
The existing digest-pinned process launch binds the actual worker image.

`qualify-v2` adds one explicit policy argument after the existing positional
qualification arguments. It selects fixed settings: arena empty,
entry-closure `1`, debug-match empty. Parent and worker receive explicit values;
the worker uses the existing Windows process owner, 90-second timeout and
512-MiB memory budget, with 30-second action deadlines and 10-second shutdown.
The old qualifier path remains V1. V2 evidence requires a policy-specific marker
after executed checks; V1 evidence cannot certify canonical V2 identities, and
malformed reserved V2 identities never fall back to V1 interpretation.

Executable unit specs and companion manuals cover identity mutation, closed
CLI, actual parent-header scope, filesystem receipt admission and evidence
framing. The real process evidence function uses existing captured-write
regression source and actual clean parent output. Runtime execution is deferred
to root's admitted resource envelope. Sidecars N/A; merge owner root; highest
review required before integration; no push authorized by this artifact.
