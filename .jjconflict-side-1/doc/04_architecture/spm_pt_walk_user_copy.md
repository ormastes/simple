# SPM pt-walk user-copy Architecture

Feature: FR-SPM-0001.

`src/os/kernel/memory/vmm.spl` owns page-table traversal. IPC code may validate
grant ranges and request copies, but it must not decode page-table entries or
invent alternate user-pointer dereference paths.

The explicit-space helpers walk `ProcessVmSpace.pml4`, translate each touched
page to a physmap kernel pointer, and return failure instead of falling back to
identity mapping. pml4-less fixtures are treated as test/early-boot state and
remain VMA-only until a real process page-table root is available.
