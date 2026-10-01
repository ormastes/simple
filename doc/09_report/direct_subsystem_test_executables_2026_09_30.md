# Shared Windows/Linux subsystem test fixes — 2026-09-30

These changes use one source revision on both platforms. They concern direct
test executables, not building the generic test runner.

| Entry | Implemented coverage | Runtime status |
| --- | --- | --- |
| `src/compiler/10.frontend/core/test_core.spl` | 68 existing compiler checks preserved in order; owning scope counts failures and controls process exit | UNEXECUTED |
| `src/compiler/10.frontend/core/interpreter/test_interp.spl` | 103 existing static check calls; failed or empty runs now exit nonzero | UNEXECUTED |
| `src/compiler/99.loader/test_loader.spl` | Three real loader-intent cases: metadata registration, rejecting source as SMF, and cache intent isolation | UNEXECUTED |

Static call counts are not executed-test counts. The loader entry is an intent
smoke test, not the full loader suite or relocation coverage. The original
loader-intent SSpec shares its production case functions and includes missing
fixture coverage. Two additional SSpec files exercise actual shared verdict
and compiler-check helpers, including failure accumulation and empty runs.

## Defects corrected

- The compiler integration entry previously printed failures without a failing
  process status. Checks now return failure counts; the calling scope owns
  accumulation, avoiding the documented shared-state mutation limitation.
- The interpreter entry previously printed failed results but did not set a
  failing exit status. It also no longer labels zero execution as success.
- A direct loader-intent executable entry is now available without compiling
  the generic CLI or test runner first.

## Evidence and qualification

Source review and focused whitespace checks passed. A static comparison
confirmed preservation of the compiler entry's 68 original checks and order.
Native executable builds, SSpec execution, generated manuals, and Windows/Linux
runtime verification remain unexecuted. No executable PASS or release readiness
is claimed.

After establishing valid producer/runtime/input bindings, use the pure
positional native-build route for each entry. Keep independent caches under
`build/bootstrap/tool_cache/<producer-phase>/<producer-sha>/<subsystem>` and run
the output from the repository root. Record producer provenance separately from
the tested source revision; different revisions alone do not establish a defect.
Do not use a seed-delegated spec result or an SMF artifact as evidence of a
native PE/ELF test executable. Existing restricted investigations were not resumed.

## Platform comparison

The historical Windows Phase 3 diagnostic launcher omitted the backend
composition source root and selected the fail-closed `unselected` module.
The corresponding Linux launcher included that root first. Current canonical
Windows/Linux bootstrap recipes already share the correct composition-first
ordering, so no canonical recipe change is included here. The observed HIR
totals came from different revisions and inputs and do not isolate an OS defect.
