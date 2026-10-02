# DevHub and mail Phase 1 acceptance — 2026-10-02

STATUS: WARN — targeted Confluence checks pass; compiled mail helper and remaining
mail acceptance are pending. This is not release admission.

## Producer and execution boundary

The user explicitly selected the Phase 1 compiler for this work. Tests ran with
`test <spec> --mode=interpreter` using the Rust bootstrap producer below; executed
example counts were observed, rather than inferred from file loading.

- Path: `D:/dev/manager-bootstrap-verification-20261001/corrected-seed-release-0d722af3/target/x86_64-unknown-linux-gnu/bootstrap/simple`
- SHA256: `4ad9c9f7444e625b384f5ceb6ea3144b126e5fc892a6e14e811313ba6f7c2992`
- Host: WSL Debian, Linux x86_64; no Windows/macOS/BSD runtime claim.
- Each target: cgroup memory.max 1073741824, pids.max 512, one CPU, timeout 300s.
- Logs: `D:/dev/devhub-mail-phase1-evidence-20261002/<lane>/` contains producer
  hash, stdout/stderr, exit, memory peak/events, and remaining owned PIDs.
- Descendants were contained in the private cgroup and killed after result
  capture. Runtime daemon warnings remain in the raw evidence.

## Observed results

| Lane | Executed | Passed | Failed | Peak bytes | Result |
|---|---:|---:|---:|---:|---|
| Final Confluence SOSIX SSpec (`confluence-sosix`) | 17 | 17 | 0 | 639754240 | PASS, exit 0 |
| DevHub config regression (`confluence-config-regression`) | 32 | 32 | 0 | 539357184 | PASS, exit 0 |
| Shared SDN first attempt (`shared-sdn`) | 6 | 3 | 3 | 600821760 | FAIL, exit 1 |

The first SDN run found a real JSON constructor defect: an array of key/value
pairs was passed to a dictionary-taking constructor. The three account scenarios
failed with `method keys not found on type array`. Literal-secret rejection,
malformed-SDN rejection, and invalid-port rejection passed. The defect was fixed;
those three unchanged passing bodies were moved to
`shared_mail_sdn_validation_spec.spl` without rerunning them. Corrected account
scenarios also cover the user's subsequently selected nested `email` scope.

The earlier Confluence run passed 17 examples before the requested SOSIX migration;
it is superseded by the final run, not counted twice. All final Confluence and
config scenarios have zero skipped/dropped examples and no cgroup OOM events.

## Documentation and review gates

Pinned-producer `spipe-docgen <spec> --output doc/06_spec --no-index` generated all
four mirrored manuals: Confluence access, POP3 credentials, shared mail acceptance,
and shared mail validation. Every invocation exited 0 and reported 1/1 complete,
0/1 stubs. Manual review found scenario steps plus folded executable SSpec blocks.
The generator reports documentation-length/metadata warnings for concise specs;
it also folds the full manual in its default presentation. Neither warning is
represented as execution evidence.

Working/staged direct-env-runtime guards and numbered-artifact guards passed.
The `doc/06_spec` executable `*_spec.spl` inventory was zero. Only named lane files
are staged; unrelated baseline LFS nonpointer warnings and generated runtime state
are excluded.

## Remaining gates

- Compile the real config-json helper from the final nested-email parser revision,
  retain its producer/source identity, and supply MAIL_CONFIG_BIN to mail fixtures.
- Execute corrected shared account scenarios and the 10-scenario POP3 system spec,
  including real curl loopback TLS/STLS, strict LIST IDs, and credential redaction.
- Finish required broader compiler/core/lib and MCP smoke checks for the SOSIX
  facade change before any blanket production-readiness PASS.
- Root final review and release-branch landing; this report never authorizes
  relabeling the bootstrap producer as self-hosted or native release evidence.

Live service access, live email sending/deletion, real account secrets, and
cryptographic implementation validation are outside these offline fixtures.
