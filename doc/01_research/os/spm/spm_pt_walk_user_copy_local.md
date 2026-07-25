# SPM pt-walk user-copy Domain Research

Feature: FR-SPM-0001.

Kernel user-copy paths normally split validation from copying:

- Check the user pointer range before dereference.
- Walk or pin each touched page, because a buffer may straddle a page boundary.
- Fail the whole copy when any page in the range is unmapped or lacks required
  user access.
- Keep unsafe memory access centralized in the VM layer rather than spreading
  raw user-pointer dereferences across syscall handlers.

The implementation follows that shape by keeping page-table decoding in VMM and
having IPC code consume explicit `ProcessVmSpace` helpers.
