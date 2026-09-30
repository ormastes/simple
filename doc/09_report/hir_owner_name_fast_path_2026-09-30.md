# HIR owner-name fast path verification

Portable source base: `a56d696c65ecca8bd440d4589574e892d07dce4d`.
Isolated Git lane: `D:/wk-hir-owner-perf-20260930`.
Frozen-producer probe lane: `/mnt/simple-bootstrap-6b2/hir-owner-perf-fix-20260930`.
Live audit: `/mnt/simple-bootstrap-6b2/frontend-perf-audit-20260930/report.md`.

## Static review

The fast path accepts only nonempty ASCII identifier segments separated by
single dots. Each segment begins with a letter or underscore; subsequent
characters can include digits. Every accepted input is unchanged by slash
normalization, numbered-directory stripping, identifier sanitization and
numeric-segment removal. `std` aliases and extension-looking suffixes are
explicitly excluded. Thus the fast return preserves the old owner identity.

The slow path is copied unchanged from the previous private helper. There is
no global memo, environment access, heap promotion, symbol-table field or
codec change. Tests import the extracted production helper; the old algorithm
is a separate differential oracle. Unicode cases contain real Unicode text.

## Focused native evidence

The probe uses the retained 908 producer, its retained core C runtime, explicit
no-stub policy, disabled frontend cache and an isolated frozen input copy.
The running Phase 3 input is untouched. Full compiler/spec checks are not
substituted by this focused diagnostic.

Attempt 1 compiled the production normalizer and common path module, then
failed on an LLVM duplicate declaration for the reference oracle in the entry
module. The oracle was separated into a fixture module; attempt 2 exposed a
test import path unsupported by this producer. The final fixture uses its
sibling module import. These failures and raw logs are retained in the probe
lane. No successful result is inferred from compilation of individual modules.

Provenance correction: attempt 1 inherited the scope-probe owner's cache
environment variable despite a private `--cache-dir` argument. It exited after
four seconds, and the scope-probe owner was notified. No files were removed
from that cache. Later attempts explicitly set the private cache environment
variable as well as the command-line argument.

Final attempt: all five native objects compiled; linking failed because the
frozen source lacks `tools/counterpart/sdk/c/simple_counterpart_abi.h`, included
by `src/runtime/counterpart_abi_runtime.c`. Compile exit: 1; elapsed: 32.148 s.
`result.json` and `compile.log` retain that failure. The executable and run log
do not exist, so the differential assertions and allocation counter have not
executed. The three-attempt limit was reached; no further build was launched.

STATUS: WARN — implementation and native object compilation complete; runtime
regression/allocation evidence and full SymbolTable tests pending.

No full-build speedup or memory-leak claim is made. Paired full-closure CPU,
boundary-memory and semantic-output comparison remains required for those
claims. The existing qualified SymbolTable spec remains an additional gate for
a qualified full test runner.
