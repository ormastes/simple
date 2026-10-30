# Test runner semantic library-mode transport

Source: `test/01_unit/lib/test_runner/library_mode_transport_spec.spl`.
Status: **NOT_RUN**. Sixteen authored cases; zero executed. This manual describes
assertions and required future evidence, not a compiler or backend PASS.

The canonical `simple test` request carries `TestOptions.library_mode`, default
empty. It uses the compiler's existing semantic policy and forwards the exact
token through parallel test children and explicit native-build children. A host
runner's own configured family does not select a child's family. No environment
variable, physical source directory, global NoGC switch, or fallback ordering
substitutes for the request.

| Case | Actual assertion |
|---|---|
| Unset compatibility | Empty field, interpreter route, exact prior child/build argv |
| Value consumption | Two-token mode is not a positional path; host gc_off unchanged |
| Shared semantics | All nine policy tokens validated by the same compiler owner |
| Connected forwarding | Exact parallel argv reparsed and used by native command builder |
| Request isolation | NoGC, GC, unset requests retain their own independent values |
| Legacy namespace | Exact pre-change executable path and source identity when unset |
| Profile namespace | Same producer/spec/time gives distinct GC/NoGC executable/cache paths |
| Invalid values | Same diagnostic as canonical policy for malformed tokens |
| Missing/duplicate | Missing and repeated selections fail with attributable diagnostics |
| Unsupported route | Interpreter, legacy native-SMF and compile-only selection refused |
| Contradictory mode | Explicit interpreter/SMF/auto/compile/JIT refused in either argv order |
| Legacy precedence | Unset mode retains existing native-backend precedence |
| Alternate transport | Safe and composite execution routes refuse lost selection |
| Doctests | Explicit and config-enabled doctest lanes refuse unsupported transport |
| Resume argv | Both flag orders and mode spellings refuse profile-unbound checkpoint totals |
| Effective resume | Final merged resume option refused; empty-mode legacy resume retained |

Selected-profile resume is not qualified: legacy checkpoints do not identify a
library profile. The runner rejects it both during argv validation and after
effective request defaults, before discovery, checkpoint reads, completed-file
filtering or carried totals. This is a refusal, not a new checkpoint format.

The artifact namespace hashes the previous ordered-source identity plus a
versioned, length-delimited semantic mode only when selected. The private cache
remains exactly `<artifact>.cache`; the same versioned identity enters execution
metrics. Native-build already binds the semantic profile into compiler closure
identity. Existing receipts retain exact argv and output path. Legacy bytes and
paths remain unchanged when no mode is supplied.

## Required actual Phase 3 preflight

Do not execute with a seed, a compiler merely named stage3, or an unadmitted
artifact. The coordinator first records actual producer SHA256, parent lineage,
source commit, selected runtime hash, configured owner selection, successful
Hello execution, and the existing owned-process resource receipt. Keep normal
5,859,375 KiB tree enforcement, bounded compile/run deadlines, and the existing
cumulative attempt ledger. No test or compiler was launched for this change.

With that admitted compiler and canonical production runner, run the existing
fixtures `test/fixtures/test_runner/native_framework/hooks_and_siblings_spec.spl`
and `failure_continuation_spec.spl` using:

`simple test <fixture> --native-backend llvm --library-mode <profile> --native-source src/compiler --native-source src/app --native-source src/lib --sequential --no-cache --no-db --no-session-daemon --assert-ran --keep-artifacts`

Use generic source roots. Bind `SIMPLE_BINARY` to the admitted native producer
and `SIMPLE_RUNTIME_PATH` to its admitted compatible runtime as required by the
existing executor; neither variable chooses a library family. The canonical
runner itself must be built through its genuine production entry with its own
effective configuration, not a replacement test framework.

Interleave `nogc-sync-mut`, `gc-sync-mut`, then the first profile again. A missing
selected framework owner is a real failure requiring resolution, not permission
for cross-family fallback. For each supported profile, positive must execute
3/pass3/fail0/exit0. Negative must execute3/pass2/fail1/exit1 with the deliberate
matcher failure, later bodies and after hooks observed. Compiler failure,
process admission failure, a crash, timeout, or zero cases cannot satisfy either
oracle. Retain exact native invocation, selected-owner/cache identity, artifact
hashes, real case counts, stdout/stderr and terminal resource/cleanup receipts.

Execute this 16-case spec through the same real framework. Also exercise invalid,
duplicate and unsupported CLI selections as separate processes: exit2 and the
specific diagnostic, with no native compile admission. Include selected-profile
`--resume` with a retained prior checkpoint: require `TEST_LIBRARY_MODE_RESUME`,
no checkpoint read/delete, no skipped-file reuse and no carried totals. The structural command
and identity cases do not replace these compiled preflights. Do not repeat a
passing criterion unless a changed implementation or new concern justifies it.
