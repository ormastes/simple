# Cert Redeploy Kit — runtime/interpreter defect fixes

Design docs + source fixes + expected-behavior specs for the runtime/interpreter
defects found by the tool-qualification corpus
(`test/cert/tool_qual/known_defects/`).

## Execution-engine finding (important context)
`simple run <file>` does NOT use the Simple tree-walking core interpreter
(`src/compiler/10.frontend/core/interpreter/`). It uses the Rust seed's cranelift
JIT + native runtime (`src/compiler_rust/**`). Evidence:
- Value display tags (`<array@0x...>`, `<invalid-heap:...>`, `<value:...>`) come
  only from `src/compiler_rust/runtime/src/value/sffi/io_print.rs`.
- The `[INFO] JIT compilation failed, falling back to interpreter` message comes
  from `src/compiler_rust/driver/src/exec_core.rs`.
- The core interpreter's `val_to_text` already renders arrays as `[1, 2, 3]`,
  yet the binary prints `<array@0x...>` — so that path is not taken.

Consequence: all six defects live in the frozen Rust seed (runtime + JIT
codegen). None are pure `src/lib`, so none are end-to-end verifiable against the
frozen deployed binary without a seed rebuild + redeploy.

## Status
| # | Item | Layer | Fixed? | Verified |
|---|------|-------|--------|----------|
| 01 | `print(array)` value display | runtime `io_print.rs` | YES | Rust unit tests (cargo, now) |
| 02 | closure return across fn boundary | JIT closure ABI | no (root-caused) | redeploy-pending |
| 03 | inherited trait default segfault | JIT vtable | no (root-caused) | redeploy-pending |
| 04 | mixin `use` (class garbage / struct not wired) | injection + JIT layout | no (root-caused) | redeploy-pending |
| 05 | nested closure transitive capture | JIT closure capture | no (root-caused) | redeploy-pending |

## Honesty note
Only item 01 is fixed and verified (at the Rust unit-test level; end-to-end is
redeploy-pending). Items 02–05 are root-cause analyses with expected-behavior
specs; their fixes are in the frozen cranelift JIT codegen and were NOT
implemented/verified in this change. No fix is claimed to "work" on the frozen
binary. Redeploy-pending specs live in `test/cert/redeploy_pending/` (a dir the
normal suite does not run) so a red-until-redeploy test never breaks the suite.
