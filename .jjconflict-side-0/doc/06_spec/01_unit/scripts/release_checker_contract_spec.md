# Release Workflow Checker Contract Specification

> **Manual draft — pending canonical `spipe-docgen`.** The executable Simple
> source contract is paired with a shell self-test that requires no QEMU,
> compiler build, or network access.

Executable sources:

- `test/01_unit/scripts/release_checker_contract_spec.spl`
- `test/01_unit/scripts/release_checker_contract_test.shs`

## Bound release artifacts

The size gate assigns distinct overrideable budgets to the portable runtime,
MCP servers, loader archives, and runtime archives. Release-path ELF/Mach-O
executables must also be stripped. Missing artifacts fail unless the caller
selects the existing `--skip-missing` policy.

## Authenticate payloads

The payload gate requires repository-identical root notices, rejects known
development caches, and compares the complete bundled font path set and bytes
with the tracked source tree. Archive paths cannot escape their extraction
root; nested archives have exactly one top-level root, and escaping symlinks or
hardlinks fail before extraction.

## Delegate platform checks

The SimpleOS wrapper invokes the canonical Simple-owned QEMU scenarios. Smoke
uses `x64-nvme-fat32`; full additionally uses `x64-full-stack`. The MCP wrapper
validates package metadata, downloads the matching Linux x64 bootstrap and
checksum from the tagged GitHub release, verifies it, and stages the exact MCP
binary named by the npm package.
