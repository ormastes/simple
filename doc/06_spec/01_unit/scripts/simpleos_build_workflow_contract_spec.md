# SimpleOS Build Workflow Contract Specification

> **Manual source contract — pending canonical `spipe-docgen`.** This check is
> intentionally static: it does not compile Simple or launch QEMU.

Executable source:

- `test/01_unit/scripts/simpleos_build_workflow_contract_spec.spl`

## Self-host before SimpleOS checks

Both x86 jobs use one bounded `--full-bootstrap` step to own Rust seed,
`native_all`, backfill, staged pure-Simple bootstrap, and deployment. It uses
Cranelift, two workers, and disables MCP. The deployed `bin/simple` must be
executable, and a version identifying a Rust seed, bootstrap seed, or
Rust-built binary fails the job.

Before either build, the workflow installs `libunwind-dev`, which the native
Stage 2 link requires on GitHub's Ubuntu runner.

## Retain bootstrap failures

Immediately after each `pure_simple_bootstrap` deployment step, an artifact
step retains `build/bootstrap/logs/**` only when that specific step failed. Its
name includes both the job identity and commit SHA, missing logs are an error,
and retention is seven days. Earlier unrelated failures cannot trigger this
upload, and the diagnostic does not make later bootstrap or evidence checks
optional.

## Fail-closed smoke evidence

The smoke job has no `continue-on-error`. It installs QEMU, LLVM, FAT tooling,
OVMF, and GRUB EFI, runs the bootstrap smoke, then invokes the WM font/input
evidence wrapper with an explicit pure-Simple binary and build-local report.
The evidence command is fail-closed; its retained report, captures, serial log,
and QEMU log upload under `always()`.

## Trigger and timeout contract

Changes to the compiler, libraries, Rust seed/runtime, bootstrap scripts,
SimpleOS sources, evidence wrapper, disk builders, or pinned font asset trigger
the workflow. Each job has 150 minutes; deployment has 60, smoke bootstrap 25,
full bootstrap 60, and WM evidence 35. The summary gate requires a successful
smoke job while allowing the conditional full job to remain skipped outside
its configured events.
