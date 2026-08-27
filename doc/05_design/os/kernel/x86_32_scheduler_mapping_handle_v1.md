# x86-32 scheduler mapping handle v1

## Scope

The canonical `TaskControlBlock` now reserves an architecture-neutral locator
for a mapping retained by `x86_32_authenticated_mapping_owner_v1`. The locator
contains only a one-based bounded owner slot and a nonzero owner generation. It
does not expose the page-directory physical address, CR3, leaf frames, or a
destruction receipt.

## Ownership boundary

The authenticated mapper remains the sole owner of its root lease and terminal
teardown state. The copyable TCB field is only a lookup key and cannot authorize
mapping, entry, or destruction. Its two fields deliberately match the stable
identity portion of the mapper receipt without embedding the receipt itself.

No present-handle constructor is available in this revision. Every canonical
task constructor, authenticated adoption path, bootstrap path, and fork path
stores the absent value. Legacy exec rejects a present locator before allocating
a replacement address space. This prevents aliasing a parent mapping during
fork and prevents abandoning a retained mapper root during exec.

## Deferred transfer

Publishing a present locator requires a future consume-once transaction owned
jointly by the authenticated mapper and scheduler. That transaction must bind
the mapper slot/generation to the exact TCB lifecycle identity, transfer the
root lease without exposing CR3, publish only after the task slot is reserved,
and retain rollback or terminal teardown authority for every failure. Until
that exists, x86-32 filesystem execution remains blocked.

The added field is appended to the C-layout TCB and advances its ABI revision
from 3 to 4, preserving offsets of all earlier fields.
