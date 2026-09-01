# SimpleOS dlmalloc ownership safety

The executable contract at `test/01_unit/os/libc/simpleos_dlmalloc_safety_contract_spec.spl` verifies checked request/page rounding, hard tracked-region admission, serialized free-list ownership, and no-mutation rejection of interior or double frees.

Its portable host harness checks overflow rejection, 16-byte alignment, reuse including a nonterminal free-block split, realloc, invalid/double-free handling, corrupted backward-link rejection, corrupted free-list self-cycle rejection, and `MAX_REGIONS` refusal without serving an untracked allocation. This is not a target-kernel or hardware execution claim.
