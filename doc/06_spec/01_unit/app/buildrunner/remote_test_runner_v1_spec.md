# Remote test producer argument admission V1

Status: **AWAITING_VERIFICATION** — source-authored specifications and manual.
No compiler, seed, argument spec, native test, or wrapper was executed. There is
no PASS or runtime qualification claim.

Source: `test/01_unit/app/buildrunner/remote_test_runner_v1_spec.spl`.
Owner under test: `src/app/buildrunner/remote_test_runner_v1.spl`,
`remote_test_options_v1`.

| Scenario | Intended assertion |
| --- | --- |
| Explicit LLVM | Native mode, split backend/source flags, and two exact ordered paths accept; options retain mode, backend, roots, and selection. |
| Explicit Cranelift | Native mode with equals backend/source flags and one exact path accepts. |
| Conflicting execution modes | Interpreter, compile, and `--compile` declarations reject even when shared parsing would normalize a supplied backend into native mode. |
| Implicit backend | Native mode without an explicit backend rejects, including `--native-source=src` which the shared parser otherwise defaults to LLVM. |
| Unsupported execution switches | Coverage, both safe-mode spellings, and disabled resource limits reject. |
| Listing or partial selection | Listing, ignored/skipped/slow selection, and planned-only aliases reject. |
| Tag filter | The actual shared parser syntax, `--tag requires-native`, rejects. |
| Different paths | Missing, additional, changed, reordered, duplicated, and implicit default paths reject against the exact admitted path inventory. |
| Invalid backend spelling | The shared parser's invalid-backend and missing-value errors are retained. |

These specs call only the argument admission helper. Existing `src/` is used for
the shared parser's source-directory validation, so execution expects the
repository working directory. They do not compile or run the selected specs.

The source wrapper now calls the real shared `run_test_file_native` after
requiring a pinned `tools/simple`, declared `tools/runtime/**` toolchain inputs,
and library inputs under `src/`. It requires explicit `native_source_roots`
whose paths stay within the verified task snapshot, selects the pinned compiler,
forces rebuilding and assertions, and disables database and parallel selection.
It refuses cached, degraded, skipped, pending, or otherwise incomplete native
results and derives the exact report from case events. It writes and reads back
the task-bound report before returning success to the outer execution owner for
completion finalization. These are descriptions of source behavior; they remain
unqualified until the actual native wrapper is executed with admitted toolchain,
plan, environment, events, and process/container cleanup evidence.
