# Mandatory Check Tiering

The repository has two mandatory-check tiers:

- `scripts/check/check-push-must-pass.shs` is the interactive committed-tree
  gate. It validates conflict/tree/rules invariants and the committed textual
  SDN ledger. Its target is approximately ten seconds for one pushed ref.
- `scripts/check/check-bootstrap-must-pass.shs` owns expensive compiler,
  native-build, full-test, device, QEMU, and benchmark evidence. It updates
  `doc/08_tracking/check/must_check_db.sdn` atomically. Each PASS retains its
  own `passed_at_utc`, evidence reference, and evidence SHA-256; automated logs
  live under `doc/08_tracking/check/evidence/<source-fingerprint>/` and are
  committed with the ledger. TODO/blocked rows use `never`.
  Schema v3 assigns every row an owner and actionable unblock condition. PASS
  rows use `unblock_condition=none`.

The registry is `config/check/must_check_gates.sdn`; it declares both bounded
push commands and bootstrap evidence rows. A `todo` or `blocked` row
is visible unfinished work and is never counted as pass. Only rows explicitly
marked `push_blocking: true` block an interactive push; all four compiler phase
rows are push-blocking.
The bounded push tier also materializes the exact pushed ref for the Rust
interpreter module-owner scan. This prevents an undeclared tracked module from
wasting a full Rust authority/bootstrap attempt while avoiding a compiler run.
When Git invokes the canonical hook for an already-up-to-date push, its empty
ref stream is reported as `PASS — 0 refs to push (no-op)`. Directly invoking
the consumer with empty input still fails; only the wrapper's explicit context
marker distinguishes a legitimate Git no-op from missing ref input. Malformed
rows and unreadable input remain failures.

## Compiler phase admission

A bootstrap completion does not promote rows merely because control reached
the end of the wrapper. The recorder first runs the Stage 2/3 full-provenance
verifier and the exact Stage 4 post-bootstrap SSpec. Stage 1 records the seed
input stamp, Stage 2 its admission receipt, Stage 3 its provenance manifest,
and Stage 4 its provenance sidecar as separate hash-bound evidence. Missing or
failed evidence leaves the ledger unchanged and fails the bootstrap.

The bootstrap wrapper supplies the output directory, exact Stage 4 binary, and
its provenance file. The completion recorder validates all four phases and then
runs every `automated` bootstrap-tier row in that same invocation. Thus an
ad-hoc successful full bootstrap refreshes the same evidence read by the next
push without a second manual must-check command.
Each automated checker is bound to that canonical validated candidate through
`SIMPLE_BINARY` plus the established `SIMPLE_BIN` compatibility name; a stale deployed binary or conflicting shell environment cannot
become bootstrap evidence.
Legacy focused checkers may retain an explicit diagnostic binary argument, but
must resolve the automated `SIMPLE_BINARY`/`SIMPLE_BIN` identity before any
legacy Stage 2 fallback. Every successful producer must also end in a standalone
`PASS` verdict; an exit status of zero or an intermediate marker alone is not
accepted by the ledger.

## Operator commands

```sh
sh scripts/check/check-push-must-pass.shs --self-test
sh scripts/check/check-bootstrap-must-pass.shs --self-test
sh test/01_unit/scripts/must_check_tiering_test.shs
```

Bootstrap automation is recorded only by the completion call made with the
freshly admitted Stage 4 identity:

```sh
sh scripts/check/check-bootstrap-must-pass.shs \
  --record-bootstrap-success \
  --output-dir <bootstrap-output> \
  --stage4-binary <exact-stage4-binary> \
  --stage4-provenance <exact-stage4-provenance>
```

A bare invocation fails closed. It cannot run automated rows or mutate the
ledger because it has no Stage 1–4 admission binding.

The Caret bootstrap suite has automated fixture-backed gates for injected
Claude/Codex/Gemini/Kimi argv/process wrapper contracts, messaging HTTP/MCP
primitives, and a bounded injected-command batch adapter with its derived
terminal view. These fixtures do not prove installed providers, production
agent-runtime lifecycle, or sustained multi-provider supervision; those remain
separate TODO rows. `caret-smux-multi-launch`
remains TODO until that manager is bound to real `os.apps.smux` sessions and
PTY lifecycle evidence. `caret-local-llm-launch`
remains TODO: Slang currently owns loader/readiness primitives but does not yet
provide a generation endpoint that Caret can call. The independent
`local_torch` provider is not accepted as Slang evidence.
Actual installed-provider launches are a separate
`caret-installed-provider-launches` TODO: `/bin/echo` proves routing and process
lifecycle without paid calls, but does not prove an authenticated provider CLI.
The existing interpreter/JIT/native engine differential is also an automated
bootstrap row; it is intentionally absent from the interactive push tier.
The exhaustive structural-tree self-test is likewise bootstrap-owned. The hook
uses the bounded `--push-tip` path, deduplicates identical ref updates, and
fails closed above two unique updates so operators split unusually broad
pushes. Ledger evidence must be repository-contained and the consumer hashes at
most 64 MiB total per validation.
The quick rules gate also extracts `rules.sdl` from the exact pushed ref; local
dirty policy cannot alter commands or floors, and `rules.sdl` is included in
the bootstrap/push source fingerprint.

Whole-tree use resolution, C runtime compilation, direct-runtime scanning,
signature provenance, performance-mechanism coverage, process-wait EINTR
coverage, guard wiring, and executable outline parsing are bootstrap-owned.
They previously consumed about 59 seconds before the bounded range/ref work;
moving them does not waive them—the textual ledger keeps every row TODO until
the bootstrap recorder retains its accepted PASS log.
Whole-tree means materialized: `check-use-target-resolves.shs` rejects sparse
tracked inputs rather than inferring missing members from absent bytes. Run it
from the complete bootstrap checkout. Its ratchet follows semantic import
identity, while source lines remain diagnostics only.
Stage 4 compiler admission and Stage 4 tooling admission are distinct. The
compiler-stage row cannot substitute for the receipt-backed 49-row CLI/MCP/LSP
matrix. Its generic receipt is not trusted by itself: the recorder reads the
committed `Stage4ToolingMatrixSummaryV1` artifact and independently requires
full scope, 49 terminal rows, no failed/blocked/remaining/required-not-pass or
optional-failed rows, `stage4_compiler_files=0`, and `overall=PASS`. Likewise,
server handler or GPU-admission tests cannot substitute for a
real configurable listener port, identical CPU/device outputs with device-hit
proof, or equivalent nginx/PostgreSQL/MySQL measurements. Binary-size and
startup rows require native Simple artifacts where specified; Rust-seed
interpreter measurements cannot promote them.
The runtime-API deletion detector similarly splits fixture proof from the hot
path: bootstrap runs `--selftest`, and push supplies an explicit committed range
to `--scan-only`. Do not use scan-only without an explicit range or treat it as
self-test evidence.

Do not hand-edit a TODO to `pass`; promotion must come from its bootstrap-owned
checker or a committed, semantically validated receipt:

```sh
sh scripts/check/check-bootstrap-must-pass.shs \
  --record-gate-pass <gate-id> --evidence <repo-relative-committed-receipt>
```

`stage4-tooling-matrix` retains its dedicated summary validator. Other external
rows use manifest mode `external-receipt` and name the registry-owned
`check-external-must-check-receipt.shs`; the recorder executes it only after
extracting the exact receipt and artifact blobs from `HEAD`. The validator—not
the receipt—defines the accepted observation matrix. It requires the common
`simple.must-check-external-evidence/v2` summary to reference separate committed
command, target, toolchain, and observation blobs. It recomputes every declared
SHA-256, checks their shared gate/source/run identity, and requires every exact
gate-specific acceptance ID to appear once as PASS in the observation blob.
The acceptance namespace is closed: any additional, duplicate, malformed,
FAIL, or BLOCKED `acceptance.*` line rejects the artifact even when a PASS for
the same ID is also present.
The summary itself must have an OpenSSL SHA-256 signature from a public key
pinned by path and hash in
`config/check/must_check_external_reviewers.sdn`. A zero exit without a final
PASS verdict is rejected. The production policy intentionally contains no key
until an independent reviewer trust root is provisioned; external promotion is
fail-closed in the meantime.

The generic receipt must name the exact gate and source fingerprint, state
`final_verdict=PASS`, and bind a separate committed artifact by
repository-relative path and SHA-256. Arbitrary text, a receipt for another
gate/source, a mismatched artifact, an unknown gate, an untrusted/invalid
reviewer signature, or a
semantically incomplete artifact is rejected. Its original PASS time carries forward across
the same source fingerprint while the identical blob/hash remains committed.
External and automated rows reset when their fingerprint changes; a newly
signed external summary must bind the new fingerprint before re-promotion.
`riscv32-riscv64-shared` also references `shared_inventory`,
`rv32_projection`, and `rv64_projection` blobs using the standard
`_path`/`_sha256` fields. Each uses schema
`simple.riscv-template-ownership/v1`, its matching inventory kind, the source
fingerprint, and sorted tab-separated `entry=<repo-path><TAB><reason>` rows.
Their union must exactly equal every owned committed `src` path mentioning
RISC-V/RV32/RV64. Shared reasons name existing bilateral consumers as
`bilateral:rv32=<path>;rv64=<path>`; sibling-only rows require a nonempty
`specialization:` reason. This proves review scope and inventory integrity, not
runtime/FPGA readiness or completion of the broader sharing target.
The push consumer reads and hashes evidence from the exact pushed revision, so
dirty, removed, or substituted live-worktree bytes cannot affect the verdict.
It cross-checks registry and ledger structure in one linear parser pass. Only
PASS rows enter the evidence-size and SHA-256 loop; TODO rows do not launch
per-field or per-row parser processes, so keeping all unfinished work visible
does not create hundreds of push-time subprocesses.
Production recording also refuses to run when fingerprinted inputs differ from
`HEAD`.
`completed_at_utc` remains `never` while any bootstrap row is unfinished; once
all rows pass it is the latest row's first PASS time, so replaying an unchanged
receipt cannot invent a later completion.

The signed summary is not a substitute for the raw retained command and
observation blobs it names. The independent reviewer's signature is the
authority boundary; repository review provisions or rotates only public trust
roots. Private keys and test keys never enter the policy. Self-test key
coverage copies the validator into an isolated fixture repository and commits a
fixture-only public-key policy there. The production validator has no policy or
key override, so a test flag cannot redirect trust while updating the real
ledger. The recorder also canonicalizes the manifest and ledger parents and
requires both to remain inside the same physical `MUST_CHECK_ROOT`; a disposable
fixture root cannot target the production ledger through split environment
overrides.

## Local hook installation

Unix-like hosts:

```sh
sh scripts/setup/install-must-check-hooks.shs --check ||
  sh scripts/setup/install-must-check-hooks.shs --install
```

Windows PowerShell:

```powershell
& scripts/setup/install-must-check-hooks.ps1 -Check
if ($LASTEXITCODE -ne 0) { & scripts/setup/install-must-check-hooks.ps1 -Install }
```

The PowerShell source follows the same launcher contract, but native Windows
linked-worktree execution is tracked as `windows-hook-installation` TODO until
the bootstrap ledger carries retained Windows-host evidence.

Linked worktrees share one Git hooks directory. Both installers therefore put
the byte-stable `scripts/hooks/pre-push-worktree-launcher` there; it resolves
the active worktree at invocation and enters that worktree's tracked dispatcher.
An absolute symlink to one checkout is invalid because it breaks sibling
worktrees. Both installers preserve an unrelated existing hook as
`pre-push.local`. The tracked dispatcher snapshots Git's ref input and supplies
it to both the local hook and the canonical repository guard. The verifier
accepts only the exact canonical guard, dispatcher, launcher, or launcher copy;
an unrelated wrapper containing a guard-name substring is not accepted.
An exact legacy guard or dispatcher payload is canonical replacement material;
it is not preserved as a local hook, because preserving a dispatcher would
recursively invoke itself.
The dispatcher detects that exact duplicate and does not execute it twice;
non-identical local hooks remain chained and fail closed.
