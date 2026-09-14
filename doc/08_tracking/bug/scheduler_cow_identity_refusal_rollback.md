# Scheduler COW identity-refusal rollback lacks an owned root receipt

Status: open prerequisite; physical rollback evidence **MissingEvidence**.
Date: 2026-09-14.

`sched_clone_task_impl` rejects unavailable/synthetic parent and child roots
before reserving a paired task/lifecycle identity. If a valid non-x86 shallow
COW root is returned and the identity allocator then refuses the operation,
the scheduler publishes no child, but the candidate root remains allocated.

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
new candidates nor free a shared parent subtree. This source-order correction
does not qualify non-x86 fork, rollback, or physical execution.

Acceptance evidence must fault-inject identity exhaustion and owner unlock
failure after a real prepared COW candidate, observe unchanged live parent
mappings/reference counts, verify no child publication, and confirm every
candidate is either retired or retained by an enumerable bounded owner.
