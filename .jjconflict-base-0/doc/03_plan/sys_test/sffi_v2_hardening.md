# System Test Plan: SFFI v2 Hardening

**P0 executable:** `test/03_system/compiler/sffi_v2_p0_fail_closed_spec.spl`

**Manual mirror:** `doc/06_spec/03_system/compiler/sffi_v2_p0_fail_closed_spec.md`
**Status:** P0 executable authored by a parallel implementation lane; broader
P0/P1 coverage remains planned. The current executable's provisional
`REQ-SFFI-V2-P0-001/002` labels must be aligned during merge to canonical
`REQ-SFFI-V2-001`–`008`; the requirements document is authoritative.

## Reproduce first

Run the existing focused evidence once before fixes:

1. declared return enforcement spec and fixtures;
2. unresolved extern weak-stub spec and all keyword/attribute positive controls;
3. SFFI byte-array not-option and defect-class specs;
4. unsafe capability vocabulary and resource SFFI pilot.

Do not weaken RED fixtures or accept a different engine as substitute evidence.

## Scenario groups and traceability

| Group | Requirements |
|---|---|
| Return origin and declared type | 001–004 |
| Missing symbols/conversion/function pointer | 005–008 |
| Native/freestanding provider closure | 009 |
| Crypto/entropy typed failure | 010 |
| Honest test verdict and cross-lane parity | 011–012 |
| Contract identity/ABI/return family | 101–103, 110 |
| Unsafe foreign state and type lift | 104–106 |
| Ownership/descriptors/unwind | 107–109 |
| Generation and shared registry | 111–112 |
| Performance/diagnostic/parity/admission/coverage/native-first | NFR-001–006 |

Each numbered requirement receives an explicit `describe` label in the system
spec or a linked unit/integration evidence scenario. Requirement coverage may
not be inferred from a broad smoke test.

## Required lanes

Where supported: Rust seed interpreter, self-hosted interpreter, JIT/run,
native/AOT, sealed dynload, and SimpleOS. Linux is mandatory for P0/P1; Windows
and target-specific lanes remain explicit availability cells, never silent
skips. P4+ tamper/signature cases remain planned.

## Oracles

- exact stable diagnostic code/category;
- nonzero command/build result on rejected programs;
- absence of emitted/runnable binary for unresolved required extern;
- exact typed value category for legitimate empty/zero/None cases;
- positive implemented-extern controls;
- no fabricated symbol in object/binary evidence;
- generated contract/registry golden digest agreement.

Only built-in SPipe matchers are permitted. No `pass_todo`, constant truth, bind-
only, or empty scenario satisfies coverage. Generated-manual review and
`sspec-maintain` quality checks occur when the executable spec exists.
