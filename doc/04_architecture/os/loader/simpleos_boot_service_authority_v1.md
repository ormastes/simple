<!-- codex-design -->
# SimpleOS boot service authority v1

## Purpose

Create the first nonzero scheduler task that may launch a signed filesystem
service on x86_64, ARM64, and RV64.  This is the only boot-time authority
origin.  It is deliberately distinct from ordinary spawn attenuation.

## Inputs and trust boundary

The transaction accepts only a compiled/pinned boot policy, a sealed signed
catalog record, and an already-admitted VFS open-handle identity.  It rejects
media-provided policy, `CapabilitySet.full()`, `spawn_recipe_seed_parent_caps`,
architecture-local token constructors, task zero, unknown recipes, and an
unsealed catalog.

The policy must bind target triple, canonical executable path, artifact digest,
signer/root identity, recipe, and the exact parent grants required by that
recipe.  A boolean admission result or a path lookup is never an authority
input.

## Transaction

`boot_service_authority_create_and_schedule_v1` is the single owner operation:

1. Verify pinned policy, sealed catalog record, target, and live VFS admission.
2. Allocate a fresh nonzero task identity and lifecycle generation.
3. Mint only the policy's concrete parent grants with unique provenance IDs;
   bind each token to that task identity.
4. Install the same pledged pouch in the Scheduler TCB and the IPC capability
   manager before either owner is visible to syscalls.
5. Publish and schedule that TCB on the persistent scheduler.
6. Issue a one-shot authenticated launch lease from the scheduled task.

Any failure rolls back unpublished state and consumes/quarantines the policy
nonce.  No half-published task, reusable token ID, or IPC-only authority may
remain.

## Layering

The loader owns policy/admission projection; the scheduler owns identity,
publication, and current-task selection; the IPC capability owner receives an
immutable copy during the same transaction.  Architecture entries are thin
adapters that select their pinned target and hand the persistent owners into
this operation.  They do not mint capabilities or replace scheduler state.

## Performance and bounds

The operation is boot-only and O(number of recipe grants), with a bounded
fixed-size recipe pouch.  It makes no full-tree scan, path re-resolution, or
per-token allocation after the policy projection.  Normal launch remains a
lease snapshot plus bounded grant lookup.  Record counters for denied policy,
minted grants, publication rollback, and lease issuance.

## Required evidence

For each target, evidence must show a nonzero current task, matching
Scheduler/IPC pouches, one accepted lease, a second lease rejection, exact
target/path/digest binding, and rejection of synthetic/ambient inputs.  QEMU
server and toolchain receipts are only valid after this proof.
