# Bootstrap Deployment Rollback Contract

## Requirement

`REQ-CHECK-BootDeplRollCont-001` requires compiler and companion publication to
use one provenance-bound transaction with complete rollback.

## Scenarios

1. Deployment journals the compiler, seed delegate, UI backend, MCP server, LSP
   MCP server, and MCP digest sidecars before any destination changes.
2. A v2 receipt binds the exact candidate paths, candidate digests, prior
   artifacts, transaction entry manifest, Stage-4 candidate, and Stage-4
   provenance.
3. Rollback consumes the exact retained transaction entry manifest and restores
   or removes every entry as one new transaction.
4. macOS setup resolves only the canonical `*-apple-darwin-macho` release
   directory; stale three-part directories cannot win discovery.
5. Mutations covering source symlinks, destination symlinks, staged digest
   drift, partial swaps, tampered entry manifests, pre-existing transaction
   paths, and stale v1 receipts fail closed.

## Executable Evidence

- SPipe scenario: `test/03_system/check/bootstrap_deploy_rollback_contract_spec.spl`
- Mutation matrix: `test/01_unit/scripts/bootstrap_deploy_transaction_test.shs`
