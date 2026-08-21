# Mandatory Check Tiering

The repository has two mandatory-check tiers:

- `scripts/check/check-push-must-pass.shs` is the interactive committed-tree
  gate. It validates conflict/tree/rules invariants and the committed textual
  SDN ledger. Its target is approximately ten seconds for one pushed ref.
- `scripts/check/check-bootstrap-must-pass.shs` owns expensive compiler,
  native-build, full-test, device, QEMU, and benchmark evidence. It updates
  `doc/08_tracking/check/must_check_db.sdn` atomically. Each PASS retains its
  own `passed_at_utc` and evidence reference; automated logs live under
  `build/must-check/<source-fingerprint>/`. TODO/blocked rows use `never`.

The registry is `config/check/must_check_gates.sdn`. A `todo` or `blocked` row
is visible unfinished work and is never counted as pass. Only rows explicitly
marked `push_blocking: true` block an interactive push; all four compiler phase
rows are push-blocking.

## Compiler phase admission

A bootstrap completion does not promote rows merely because control reached
the end of the wrapper. The recorder first runs the Stage 2/3 full-provenance
verifier and the exact Stage 4 post-bootstrap SSpec. These bind Stage 1 runtime
authority, Stage 2 and Stage 3 sanity/admission receipts, and the Stage 4 binary
and provenance sidecar. Missing or failed evidence leaves the ledger unchanged
and fails the bootstrap.

The bootstrap wrapper supplies the output directory, exact Stage 4 binary, and
its provenance file. The completion recorder validates all four phases and then
runs every `automated` bootstrap-tier row in that same invocation. Thus an
ad-hoc successful full bootstrap refreshes the same evidence read by the next
push without a second manual must-check command.

## Operator commands

```sh
sh scripts/check/check-push-must-pass.shs --self-test
sh scripts/check/check-bootstrap-must-pass.shs --self-test
sh test/01_unit/scripts/must_check_tiering_test.shs
```

Run the bootstrap-owned automated gates with:

```sh
sh scripts/check/check-bootstrap-must-pass.shs
```

The Caret bootstrap suite has automated gates for Claude/Codex/Gemini/Kimi
wrappers, agent-manager messaging primitives, and the bounded parent-owned
multi-Caret manager with its derived terminal view. `caret-smux-multi-launch`
remains TODO until that manager is bound to real `os.apps.smux` sessions and
PTY lifecycle evidence. `caret-local-llm-launch`
remains TODO: Slang currently owns loader/readiness primitives but does not yet
provide a generation endpoint that Caret can call. The independent
`local_torch` provider is not accepted as Slang evidence.

Do not hand-edit a TODO to `pass`; promotion must come from its bootstrap-owned
checker or retained receipt validator. PASS may carry forward only while the
source fingerprint is unchanged; a changed fingerprint resets unrerun rows to
TODO instead of laundering stale evidence into the new source state.

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

Both installers preserve an unrelated existing hook as `pre-push.local`. The
tracked dispatcher snapshots Git's ref input and supplies it to both the local
hook and the canonical repository guard. The repository hook verifier accepts
only the exact canonical guard or exact tracked dispatcher path; an unrelated
wrapper containing a guard-name substring is not accepted.
