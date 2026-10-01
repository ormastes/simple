Reviewed the modified producer and untracked focused test. No edits, builds, tests, or Git mutations performed. Whole-tree enumeration failed because `git-lfs` is unavailable; scoped inspection succeeded.

**Confirmed defects**

- **Junction rejection:** [producer:207](C:/Users/ormas/dev/simple/scripts/setup/materialize-symlinks-windows.shs:207) compares `Resolve-Path` strings: `…\dir-link` versus `…\target-dir`, then exits 4. These are different names for the same directory. The positive [test:60](C:/Users/ormas/dev/simple/test/01_unit/scripts/materialize_symlinks_windows_test.shs:60) therefore fails after creation. This is a static diagnosis, not a reproduced execution.
- **Unsafe path handling:** [producer:236](C:/Users/ormas/dev/simple/scripts/setup/materialize-symlinks-windows.shs:236) embeds paths in PowerShell source: apostrophes break quoting and permit injection. Environment-variable transport used by validation is safer. [Line 285](C:/Users/ormas/dev/simple/scripts/setup/materialize-symlinks-windows.shs:285) parses quoted Git output without decoding; default Unicode quoting breaks the Unicode fixture. Command substitution also strips trailing newlines from target blobs.
- **Incomplete receipt proof:** that pipeline masks `git ls-tree` failure; both counts derive from its potentially empty output. [Hashing/publication:440](C:/Users/ormas/dev/simple/scripts/setup/materialize-symlinks-windows.shs:440) lacks strict digest validation; the output group can mask `cat` failure. Hashes cover records only and provide no authenticity.
- **Publication hazards:** [producer:102](C:/Users/ormas/dev/simple/scripts/setup/materialize-symlinks-windows.shs:102) uses predictable temporary files and check-before-create operations. Cleanup can delete an unowned collided receipt temporary. [Line 465](C:/Users/ormas/dev/simple/scripts/setup/materialize-symlinks-windows.shs:465) permits overwriting a concurrently created destination.
- **Pending/fixture mismatch:** [target resolution:159](C:/Users/ormas/dev/simple/scripts/setup/materialize-symlinks-windows.shs:159) requires existing parents, so `build/missing.exe` cannot produce the expected pending receipt. [Test:92](C:/Users/ormas/dev/simple/test/01_unit/scripts/materialize_symlinks_windows_test.shs:92) calls an untracked missing target “dangling,” contradicting producer policy. The ordinary-directory fixture’s index entry is not restored after `git add -A`. Real `bin/bb`, `bin/bug`, `bin/jira`, and `bin/mail` target optional tool trees.

**Validation and remaining risks**

[Validator:205](C:/Users/ormas/dev/simple/scripts/setup/materialize-symlinks-windows.shs:205) searches all `fsutil` text and ignores its exit status. Read the numeric reparse tag directly: junction `A0000003`; symbolic link `A000000C` requires explicit policy. This avoids localization dependence. [Microsoft tags](https://learn.microsoft.com/en-us/windows/win32/fileio/reparse-point-tags).

Use resolved handles and volume/file identity; normalize relative targets against the link parent, absolute/native prefixes explicitly. `ResolveLinkTarget` needs runtime compatibility checking: `powershell.exe` normally uses .NET Framework. [Microsoft runtime differences](https://learn.microsoft.com/en-us/powershell/scripting/whats-new/differences-from-windows-powershell).

Containment checks omit explicit reparse-ancestor inspection; MSYS junction behavior remains unverified. HEAD-pinned reads are good, but [recheck:434](C:/Users/ormas/dev/simple/scripts/setup/materialize-symlinks-windows.shs:434) cannot prevent post-check changes or filesystem swaps. Index-based pending classification is not HEAD-bound.

**Minimal patch/test plan**

- Replace directory identity/tag validation; test new/existing junctions, relative/absolute targets, Unicode, apostrophes, brackets, `$`, semicolons → pass; wrong targets, unsupported tags, denied access, loops → fail.
- Make Git enumeration byte-safe and independently checked; malformed blobs, enumeration/hash/read failure, missing/duplicate records → no passing receipt.
- Repair fixtures; tracked missing → fail/no receipt; optional missing parents → blocked receipt; ordinary directory → reject.
- Add behavioral HEAD-change, reparse-ancestor, destination-race, temp-collision, interruption, and receipt-tampering cases → reject without clobbering unrelated files.