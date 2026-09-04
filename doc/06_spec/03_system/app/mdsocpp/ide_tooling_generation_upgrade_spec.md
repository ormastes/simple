# MDSOC++ IDE/Tooling Product Generation Upgrade

## Purpose

Prove that a real userland IDE/tooling capsule can migrate persistent document
state, atomically publish a successor, drain pinned work from the old
generation, roll back while the old state is retained, and preserve bounded
receipts for every accepted phase.

## Scenarios

1. Generation 20 with document schema 1.0 upgrades to generation 21/schema 1.1.
   Revision and open-document state survive migration, while the diagnostic
   epoch advances and records generation 20 as its migration source.
2. Two old-generation requests remain pinned. The first completion leaves the
   old generation draining; the second retires it.
3. A post-publication failure rolls generation 21 back to the exact generation
   20 state while that state remains retained.
4. Too-small receipt capacity, an over-counted drain, rollback after retirement,
   and a removed migration declaration all fail closed without changing active
   authority.

## Executable Evidence

`test/03_system/app/mdsocpp/ide_tooling_generation_upgrade_spec.spl`
