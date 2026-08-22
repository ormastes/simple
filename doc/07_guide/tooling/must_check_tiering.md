# Mandatory Check Tiering

The repository has two mandatory-check tiers:

- `scripts/check/check-push-must-pass.shs` is the interactive committed-tree
  gate. It validates conflict/tree/rules invariants and the committed textual
  SDN ledger. Its target is approximately ten seconds for one pushed ref.
- `scripts/check/check-bootstrap-must-pass.shs` owns expensive compiler,
  native-build, full-test, device, QEMU, and benchmark evidence. It updates
  `doc/08_tracking/check/must_check_db.sdn` atomically. Each PASS retains its
  own `passed_at_utc`, evidence reference, and evidence SHA-256; automated logs live under
  `build/must-check/<source-fingerprint>/`. TODO/blocked rows use `never`.
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
The existing interpreter/JIT/native engine differential is also an automated
bootstrap row; it is intentionally absent from the interactive push tier.

Do not hand-edit a TODO to `pass`; promotion must come from its bootstrap-owned
checker or retained receipt validator. The push consumer opens and rehashes the
recorded evidence, so a missing or modified log/receipt rejects the push. PASS may carry forward only while the
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
