# SCV distributed textual DB production boundaries are missing

Date: 2026-09-13  
Status: OPEN  
Class: feature-blocking correctness and performance gaps  
Owner: scv-database-team

## Symptom

The selected distributed textual-database design cannot yet be implemented or
verified through production owners. The design-only system spec deliberately
fails fast. No live path currently joins typed semantic patches, compact alias
settlement, Git/CI servers, configuration-aware immutable evidence, durable
provider delivery, and retention CAS through the SJ writer boundary.

## Current source evidence

- `src/lib/scv/metadata_db.spl:117` records that insert performs a
  read-modify-write copy of the whole `SdnDatabase`; this does not meet the
  selected 10,000-observation import target.
- `src/lib/scv/metadata_db.spl:137` derives a new key from `tv.rows.len()`;
  this is unsafe for permanent shared allocation and must never allocate a
  settled alias.
- `src/lib/scv/network_remote.spl:7-13`, `:135-148`, and `:331-396` describe
  authentication/header/resumable/network behavior as stubs, simulation, or a
  future extension; this is not a production GitHub or generic Git-server
  settlement transport.
- `src/lib/nogc_sync_mut/test_runner/test_db_compat.spl` exposes mutable
  cohort/result compatibility but no immutable config/reproduction/observation/
  expectation/evaluation revision model required by REQ-016 through REQ-021.

## Unblock condition

Implement lanes L0–L10 in
`doc/03_plan/agent_tasks/simple_distributed_textual_databases.md`, replace every
fail-fast checker in
`test/03_system/app/scv/feature/simple_distributed_textual_databases_spec.spl`
with production-owner fixtures, satisfy REQ-001..REQ-036 and NFR-001..NFR-015,
and obtain final verification `STATUS: PASS`. Until then, documentation must
say design-only and no Git/CI/provider round-trip is claimed.
