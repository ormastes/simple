# Windows materializer startup shell overhead

Observed on source `52ecacbf27690be64cbeee4b59ec678baa5a4d0f`, Windows Phase1
collector 25892 started 2026-10-06T01:17:04.8760312Z. The build was not stopped
or changed for this investigation. Materialization ultimately succeeded with
61 links and zero failures; a later unrelated PATH check stopped attempt 1.

The immutable Git tree contains 175250 records (18361753 bytes). The native
validator already parses that entire tree to establish tracked-target authority.
Bash then parsed it again to select only 65 symbolic links (61 materialized and four pending aliases). The live raw tree
was complete at 01:17:26; the link list completed around 01:18:26. While links
were still being checked, Bash had consumed 76.5 CPU seconds, versus 3.5 CPU
seconds in the persistent native validator. This is shell processing overhead,
not an idle compiler or per-link repeated Git invocation.

Each receipt path also forked `tr` for every component, twice per metadata
operation. The repair emits the NUL-delimited symlink list during the existing
native strict-UTF8 tree pass and uses direct case patterns for Windows reserved
names. Drive spelling remains uppercase; other path spelling remains unchanged.

The native pass retains the existing tracked set and tree parsing behavior.
Only the small link list is streamed to disk; no second full-tree collection is
introduced. The output writer is disposed on errors. Startup must report READY
before Bash reads its output; failure leaves no consumable receipt. The existing
held-handle, identity, target-escape, policy, publication and final HEAD checks
are unchanged. Unicode names, spaces, NUL record boundaries, exact mode matching,
and `target/` exclusions must remain byte-equivalent. Optional pending aliases
retain their exact policy distinction; this change does not admit missing targets.

`scripts/check/check-materializer-startup-perf.py` exercises the actual extracted
C# and Bash helpers, compares old/new output on an immutable representative tree
and adversarial fixtures, rejects malformed input/output destinations, tests 29
valid/invalid Windows paths, and records native-helper RSS/retained allocation.
Independent groups continue after failure. This host validation does not claim
that a rebuilt Simple compiler or full bootstrap has run with this repair.

## Separate PATH startup bug

After materializer success, `bootstrap-from-scratch.sh:1494` attempted to
canonicalize an inherited protected WindowsApps PowerShell directory. `test -d`
succeeded but `cd` failed, and `|| exit 1` stopped bootstrap before compilation.
Root's process-environment workaround removed only that inherited entry and
verified required cargo/rustc/clang-cl/Windows PowerShell tools remained available.
The source remained unchanged for attempt 2. A separate repair should skip an
incidental untraversable PATH directory while retaining the empty-PATH rejection
and required tool discovery/identity checks. This patch does not change PATH policy.

## Scoped host verification

Four independent functional groups passed (including four native-helper cases
and 29 path cases), with no failing groups. Actual original Bash filtering took
93.406s versus 0.155s for the native tree pass including list generation. These
are helper measurements under concurrent bootstrap load, not whole-bootstrap
speedup claims. The 29-path before/after batch took 3.105s/0.846s. A separate
fresh-process paired memory check passed: retained allocations 31173088 versus
31173256 bytes (+168 bytes); peak RSS 191840256 versus 198885376 bytes (~7MiB
difference). The test allows 8MiB retained/32MiB RSS host noise and fails larger
increases. The complete bootstrap with this source change remains UNRUN.
