# Scheduler COW identity-refusal rollback lacks an owned root receipt

Status: unsafe ordering fixed; owned-COW rollback remains an open prerequisite
with physical evidence **MissingEvidence**.
Date: 2026-09-14.

The unsafe ordering reserved a paired identity after a valid non-x86 shallow
COW root. Identity refusal then published no child but left the root allocated
and could leave parent permissions changed. Reporting that gap alone does not
make the ordering safe.

`sched_clone_task_impl` now rejects an unavailable/synthetic parent and a full
task table, then reserves the pair before invoking COW. Identity refusal
returns before root allocation or parent mutation. Later COW failure burns the
already-issued pair; it never rolls the allocator back or publishes a child.

The current non-x86 `vmm_cow_clone_pages` returns only a raw root and shares
parent page-table subtrees. `destroy_user_address_space` recursively frees
user-half tables, so applying it to this shallow candidate can destroy live
parent mappings. No AddressSpace generation may be invented to pretend that
the scheduler holds a retirement authority. The x86 provider already returns
zero before allocating or altering the parent.

Required owner work: return a retained COW preparation/rollback capability
covering root, shared references, and parent permission changes; close that
capability on every post-COW refusal and retain an explicit quarantine receipt
on indeterminate cleanup. Repeated allocator-refused forks must neither leak
new candidates nor free a shared parent subtree. Only after this owner exists
may identity reservation move after COW. The current safe ordering does not
qualify non-x86 fork, rollback, or physical execution.

Current ordering coverage must show identity exhaustion and allocator unlock
failure return before invoking COW, and a later COW failure publishes no child
while leaving the issued identity spent. Future rollback acceptance evidence
must inject failure after a real COW preparation, restore live parent mappings
and reference counts, and confirm every candidate is either retired or retained
by an enumerable bounded owner before later identity reservation is permitted.
