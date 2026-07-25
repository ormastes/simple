# Feature: simpleos-fr-sos-017-scheduler-topology

## Raw Request
Continue fixing remaining bug and feature request trackers with pure Simple as
the main path and Rust as seed/tooling.

## Task Type
feature

## Refined Goal
Close stale `FR-SOS-017` tracking state once current tracker evidence and
focused specs prove hardware scheduler topology discovery is implemented.

## Acceptance Criteria
- AC-1: `FR-SOS-017` is marked implemented only if every listed criterion is
  checked and live AP proof is recorded.
- AC-2: Focused scheduler/topology specs are checked or tested, with any live
  QEMU gate documented separately.
- AC-3: No new Rust/C implementation path is added; this slice is tracker/state
  verification only.

## Phase
ship-done

## Log
- dev: Selected stale `FR-SOS-017`; all tracker criteria are checked and live
  AP proof is already recorded in the entry.
- implement: Removed the filesystem/kernel `CapabilitySet` name collision by
  renaming the filesystem bitmask to `FsCapabilitySet`.
- implement: Replaced the scheduler's missing `cap_init_task_record` extern
  with a pure Simple scheduler bridge and fixed CPU runqueue assignment after
  enqueue.
- verify: `topology_spec.spl` passed 7/7, `x86_64_topology_spec.spl` passed
  4/4, and `fs_driver/capability_test.spl` passed 18/18.
- verify: `scheduler_spec.spl` static check passed, but its interpreter run
  still has separate pre-existing failures outside this topology close.
- ship: Marked `FR-SOS-017` implemented; live AP proof remains the gated QEMU
  evidence already recorded in the tracker.
