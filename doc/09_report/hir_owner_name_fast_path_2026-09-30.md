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

## Link-only setup completion and first execution

The parent subsequently authorized hydration of the exact tracked counterpart
ABI header and completion of link setup using existing objects. The header was
read from retained revision `0dedfd36ee57ecb6f53b1df163268e82219ff172`; its hash is
in `header-hydration.json`. No compiler frontend was invoked. Five user and 36
runtime cache objects retained their exact hashes and timestamps. Four missing
runtime support objects and the canonical Linux entry shim completed setup.

Linking exposed an independent producer alias-emission defect: the same oracle
function appeared in both logical and physical module objects. `nm` output and
`objdump -dr` instruction/relocation streams were identical. The diagnostic link
omitted only the redundant logical alias; both cache files remain intact.
No multiple-definition suppression flag was used. The full link input manifest
and equivalence evidence are under `link-resume/`; this does not qualify the
producer's normal linker route.

The first executable reached allocation measurement without a mismatch in the
32 differential cases. It then exited **5**, failing the zero-allocation budget:

| 256 canonical calls | Registered object growth | Objects/call |
|---|---:|---:|
| Fast path | 1,536 | 6 |
| Previous algorithm | 20,224 | 79 |

This is 92.4% less registered-object growth in this fixture, but the requested
allocation-free behavior is **not achieved**. No CPU-time speedup was measured.
The first runtime failure ended validation; no further semantic fix/retry was
performed. `run.log` and `link-resume/final-result.json` are authoritative for
the actual execution; the earlier `result.json` remains the failed full build.

STATUS: FAIL — zero-allocation acceptance unmet. Differential fixture reached
the measurement successfully; full SymbolTable tests remain unexecuted.

## Separate memory event

The parent reported a WSL global OOM at 10:24:04 killing `simple.rejected` with
17,355,696 KiB anonymous RSS, and CLI host PID 690815 exiting 137 in that
interval. Exact namespace mapping was pending. This is separate from the
earlier Phase 3 PID 656341 samples (4.37/6.08 GiB RSS); neither event proves a
leak or attributes that OOM to the sampled Phase 3 process. No RSS cap was added.

No full-build speedup or memory-leak claim is made. Paired full-closure CPU,
boundary-memory and semantic-output comparison remains required for those
claims. The existing qualified SymbolTable spec remains an additional gate for
a qualified full test runner.
