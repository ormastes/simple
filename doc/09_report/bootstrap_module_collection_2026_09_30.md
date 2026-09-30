# Bootstrap constituent-module collection — 2026-09-30

## Implemented scope

Full-profile phase verification now inventories the configured composition,
compiler, app, and library source roots for independent diagnostic object builds,
even when executable builds fail. This is a conservative source-root superset,
not proof of an exact binary dependency closure or all-repository coverage.
Phase 2/3 use the available compiler's supported object-output environment mode;
the failed full CLI is not a prerequisite. Strict Stage 4 output restrictions
and source/runtime admission checks remain enforced.

Workers retain separate phase/producer/input/module caches, collect terminal
results in manifest order, reject non-object outputs, and reap owned children.
Host collection and CI fail-fast policy remain selectable. Object results do
not qualify executables or release artifacts.

The positional bootstrap CLI also has a source fix for silently ignoring
`--emit-object`, with archive/shared option parity and environment restoration.
Eight behavior scenarios were added; their execution and docgen are pending.

## Executed evidence

- Three changed Linux fixture verification groups passed, covering scheduler
  policy/cache isolation, failure aggregation, snapshot guards, production
  wiring, full/slim scope, authority boundaries, and failed source discovery.
- The Windows MSYS fixture run exited 1 because this filesystem did not enforce
  `chmod -x`. The test now explicitly skips that unsupported permission case.
- Final object validator accepted a real 566-byte COFF x86-64 object and rejected
  the Linux `/bin/sh` executable.
- An isolated Phase 2 diagnostic producer compiled a no-main function module
  with `SIMPLE_NATIVE_BUILD_EMIT_OBJECT=1`: exit 0 in 5.875 seconds. Independent
  object inspection found the `double` symbol. The preceding flag-only attempt
  failed by trying to link `__simple_main`, reproducing the CLI option bug.
- Probe evidence: `build/native_probe/module_object_probe/result2.json` and
  `object.readobj.log`. The same cache directory was retained; logs reported
  HIR hits 0, misses 1 and native cached 0. No cache-hit claim is made.

## Qualification gaps

Final fixture updates for object headers, executable rejection, worker cleanup,
and the Windows permission skip remain unexecuted under the three-cycle limit.
The final script therefore has no overall cross-platform verification PASS.
The updated CLI has not been rebuilt or exercised. No full module sweep or
Windows/Linux Phase 3/4 bootstrap was launched. Existing restricted SCV/memory
investigations were not resumed. This work is suitable for draft review only;
main/release promotion still requires the missing runtime evidence.
