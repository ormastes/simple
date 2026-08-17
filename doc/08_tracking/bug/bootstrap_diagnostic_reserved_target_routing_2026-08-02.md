# Bug: diagnostic sweep drops a source named `check_entry.spl`

- **ID:** bootstrap_diagnostic_reserved_target_routing_2026-08-02
- **Date:** 2026-08-02
- Status: CLOSED (not reproducible)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
- **Component:** `src/app/cli/check_entry.spl`
- **Severity:** diagnostic-sweep false failure

## Reproduction

The exact command used by the sweep failed without a source diagnostic:

```text
simple check src/app/cli/check_entry.spl
Usage: simple check <file.spl> [file2.spl ...]
```

The delegated check wrapper received the target as its first argument. Its
entrypoint normalization treats a first argument ending in `check_entry.spl`
as the wrapper path, so it removed the real target and printed help. Ordinary
source basenames were unaffected. This was command-routing infrastructure, not
a parser or semantic failure.

## Fix

The check entrypoint now consumes only an explicit `check` command token. It no
longer guesses that an argument is entrypoint metadata from its basename, so
every source path remains data without weakening validation or adding another
filename exception.

## Regression coverage

`test/01_unit/compiler/bootstrap/check_entry_target_routing_contract_spec.spl`
guards both the reserved-looking target and the adjacent explicit command-token
path. The exact production command is also verified directly.
