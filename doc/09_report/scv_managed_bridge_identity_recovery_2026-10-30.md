# SCV managed bridge identity and interrupted initialization

Source repair based on the managed bridge integrated on release revision
`f8b3ebb33c85e4f7c71b029018edf7dc2cb2a5f8`. Runtime verification: NOT_RUN
in this source repair lane; the assigned build/test lane must record the actual
producer identity, commands, exit status and assertion counts separately.

## Observed defects and repairs

The bridge normalized a task's attempt to zero when deriving its capture epoch.
The canonical task validator requires attempts 1 through 100, so the task
identity became empty and distinct tasks shared the same epoch prefix.
The owner now validates the original task, normalizes to valid attempt 1,
requires a nonempty canonical identity, and constructs the epoch from that
identity. Logical managed construction also rejects invalid original tasks.
Retries retain the epoch; different task subjects receive different epochs.

First initialization publishes the immutable source record before managed input
staging and managed-record publication. If staging or compiler admission failed,
a subsequent open treated that source record as a complete initialized session
and permanently required the missing managed record. The source record now
serves as durable initialization intent: an ordinary run can reconstruct the
managed record only while no scheduler journal exists. It must revalidate the
same retained source subject and exact task/context inputs before doing so.

Verification and every open with an existing scheduler journal require a retained
managed record. This also applies to sessions containing only legacy source-only
tasks. An existing managed record must match exact reconstructed bytes; a poisoned
record is never overwritten by initialization replay. The repair neither resets
capture epochs nor clears unknown state.

## Authored regression evidence

- `test/01_unit/app/buildrunner/scv_managed_session_v1_spec.spl`: valid nonempty
  epochs, retry stability, distinct task subjects, and invalid-attempt rejection.
- `test/03_system/app/buildrunner/feature/scv_source_session_v1_spec.spl`: real
  source capture followed by physical compiler substitution rejects first managed
  admission after writing the source intent; restoring the exact compiler image
  completes the same pinned session. Additional cases reject missing records
  during verification/journal recovery and preserve an actual encoded unknown
  capture record byte for byte.

These tests are authored acceptance checks, not passing execution evidence.
Compiler semantic producer completion, physical event coverage, editor overlays,
generated/external producers and managed retention-store admission remain outside
this declared-input bridge and are not authorized by its records.
