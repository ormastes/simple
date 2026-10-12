# Phase 2 capsule long-leaf ACL repair

The recovery Stage 2 build passed compiler, receiver, runtime and private-admission
probes, then capsule publication failed in Windows PowerShell 5.1 at
`FileSystemInfo.GetAccessControl()`: `Invalid name. Parameter name: name`.
The SHA-addressed staging directory plus hosted-runtime filename produced a
262-character path. The publisher cleaned its staging directory and did not
publish a successful binding. The canonical short-output-root recovery is separate.

## Change and boundary

Keep original FileSystemInfo traversal, reparse-point rejection, root/child
distinction, Everyone deny rights, and freeze/verify/thaw behavior. Convert only
ACL API paths to extended native Windows paths. DOS paths become `\\?\C:\...`;
UNC paths become `\\?\UNC\server\share\...`. Normalize separators, recognize
already extended DOS/UNC spellings, and reject unsupported path namespaces.
Use Directory/File GetAccessControl and SetAccessControl on these native paths.
Diagnostics include the operation and failing original node.

This repairs long **leaf names beneath traversable directories**. Existing
Windows PowerShell Get-ChildItem traversal still fails closed when a directory
itself exceeds its path limit. A synthetic deep-directory regression demonstrated
that separate limitation; this patch does not claim to fix it or weaken traversal.
Actual UNC access is not exercised without an available share; UNC spelling is
checked independently.

## Bounded verification on Windows, 2026-10-11

`scripts/bootstrap/tests/phase2-capsule-permissions-test.ps1` uses Windows
PowerShell and real ACL changes on uniquely owned fixtures. No seed compiler.

1. Initial run: ordinary 143-character leaf passed freeze, verify, denied file
   writes, denied namespace writes, denied child deletion, thaw, and restored
   writes. The subsequent deep-directory fixture failed traversal before ACL
   mutation. Its cleanup also failed, leaving its uniquely named fixture.
2. Revised run with `-Cases long`: production-shaped 285-character leaf passed
   the same real ACL operations. Junctions were available; freeze, verify and
   thaw rejected the reparse point, and its target ACL remained unchanged.
   Path conversion checks covered DOS, UNC, extended forms and invalid forms.
   Windows PowerShell Remove-Item then failed on the long leaf during cleanup;
   process exit was 1 despite the preceding checks passing.
3. Cleanup changed to extended-path Directory.Delete after explicit owned-root
   validation and junction removal. `-CleanupOnly` created a fresh long leaf,
   deleted its owned root and exited 0. Previously passing ACL cases were not
   rerun. STATUS is printed only after cleanup completes.

Thus each stated ACL acceptance criterion and the corrected cleanup were
executed successfully, but there is no single end-to-end all-cases exit-0 receipt
for the final test script in this session. The unchanged final ACL implementation
passed the ordinary and long-leaf cases above. Compiler/native qualification is
separate and no compiler source or frozen candidate was modified.

An automatic policy block also rejected an explicit cleanup command for the
first failed fixture; that target remains preserved rather than retried through
another command. The test's new cleanup was verified only on its fresh owned
fixture. Remaining directories are under this isolated worktree's ignored
`build/native_probe/capsule-acl-test-*` and are not source artifacts.
