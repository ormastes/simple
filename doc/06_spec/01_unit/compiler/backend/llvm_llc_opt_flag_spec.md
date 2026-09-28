# LLVM llc optimization flags

Manual companion for `test/01_unit/compiler/backend/llvm_llc_opt_flag_spec.spl`.

| Compiler optimization | llc flag |
|---|---|
| None / Debug | `-O0` |
| Basic | `-O1` |
| Size / Standard / Speed | `-O2` |
| Aggressive | `-O3` |

Size policy belongs to the IR optimization pipeline; llc receives its supported
numeric level. Basic/Standard coverage was added with retained backend target
context V2. Execution on that stack remains blocked pending an admitted
source-compatible self-hosted runtime; this table is not a test-pass claim.
