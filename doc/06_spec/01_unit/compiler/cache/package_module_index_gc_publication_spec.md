# Package index GC publication exclusion

Executable source:
`test/01_unit/compiler/cache/package_module_index_gc_publication_spec.spl`.
Requirement: `PSI-REQ-004`.

Status: **UNEXECUTED**. This is a hand-maintained scenario manual pending
admitted SSpec execution/docgen, not generated PASS evidence. The initial test
was written before the production repair; no behavioral RED/GREEN has run.

## Preserve current and candidate bytes while publication owns CURRENT.lock

1. Publish two complete valid generations with distinct content identities.
   Select one as CURRENT and leave the other as an unretained candidate.
2. Acquire the actual publication lock through a separate lock handle.
   Invoke production GC with an empty retained list and a positive limit.
3. Release the external lock and inspect the captured results. Expect zero
   removals, exact unchanged bytes for both generations, and the same CURRENT
   digest. Before the repair, source inspection predicts that GC deletes the
   non-current candidate because it does not honor the held lock; execution
   must establish the actual pre-fix failure.
4. Invoke GC with the candidate explicitly retained. Expect zero removals and
   unchanged candidate bytes.
5. Remove the retained-list protection and invoke GC again. Expect exactly
   one removal, the non-current candidate absent, and the current generation
   still admitted by the production reader.

The fixture uses production publication, encoding, locks, reads and GC. It does
not reconstruct the collector or print a predetermined success record. Distinct
lock handles provide synchronization rather than timing sleeps.

## Qualification still required

Run the same executable specification against the pre-fix and repaired source
with one immutable admitted pure-Simple runtime. Capture binary and source
digests, command, exit status, assertion counts and logs. Regenerate this manual
through the admitted docgen afterward. The current host has no validated runner.

This scenario proves only publication/GC exclusion when executed. Atomic reader
pin acquisition, crash durability, cross-process lifetime, whole-compiler cache
reuse and performance remain separate acceptance requirements.
