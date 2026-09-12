# `Array.remove_at` is not a supported native or interpreter operation

**Status:** RESOLVED (per record's own account; not independently re-verified 2026-09-12)

- Filed: 2026-09-08
- Severity: P1
- Status: language gap open; invalid Stage4 call site corrected
- Exact site: `src/lib/scv/compile_source_inventory.spl:288`

After `split_whitespace` resolution was fixed, Stage2 advanced to
`cannot resolve method call Array.remove_at`. The interpreter lists
`remove_at` as a possible mutator but its array dispatcher implements only
`remove`; LLVM likewise maps `remove`, whose contract is to mutate the receiver
in place and return the removed element.

The inventory code incorrectly assigned the nonexistent `remove_at` result
back to the array. It now uses canonical `entries.remove(found)` as a statement.
Implementing a first-class `remove_at` alias consistently across interpreter,
MIR, LLVM, Cranelift, and documentation remains a separate language task.

## Triage 2026-09-12
Body appears to state resolution; not independently re-run in this pass (rule D bulk pass). Older-than-45-days threshold does not apply (record is newer than 2026-07-29). Evidence: seed binary /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
