# A quarantined generation's own name pushes its contents past MAX_PATH, and the Stage-3 preflight then refuses every later run

Filed: 2026-09-25
Host: DESKTOP-5A4V03J (Windows 11, Git Bash / MSYS2, `x86_64-pc-windows-gnu`)
Severity: Blocking, and self-perpetuating — one failed publish disables every
subsequent phase-1 run on the host until a human deletes the quarantine by hand.

## Symptom

After a publish failure quarantined a generation, every later
`sh scripts/bootstrap/run-phase1-local.shs` aborts before any pure-Simple
stage starts:

```
stage3-materialized-consumer: Exception calling "Run" with "0" argument(s):
  "api.open:C:\Users\User\dev\simple\src\compiler_rust\target\bootstrap.generations\
   .rejected.9d12f4f079cfbc5919bbaabdeeb621a67a5d0f4a3d0c02e0e08e2d0d11fd7fe1-23802e6df3d428b984ab6768e091fa79e1ebd517a60278bb151dca62a7ab69fb.20550.0\
   deps\libspl_hosted_runtime-d33a4d50eeeb8dfd.rlib:win32=3"
ERROR — could not bind preflight source and git state before checks
error: authoritative bootstrap preflight failed; no pure-Simple stage was started
VERDICT — ABORTED: stage=fingerprint exit=1 signal=none reason=fingerprint
```

`win32=3` is `ERROR_PATH_NOT_FOUND`, which reads as "the file is missing". It is
not missing:

```
$ ls -la '.../.rejected.9d12f4f0...20550.0/deps/'
-r--r--r-- 1 yoon 197121   250674 Sep 24 17:24 libspl_hosted_runtime-d33a4d50eeeb8dfd.rlib
-r--r--r-- 1 yoon 197121 28205084 Sep 24 17:24 libsimple_runtime.a
```

## Cause

The path is **268 characters**; Windows `MAX_PATH` is 260.

```
$ P='C:\Users\User\dev\simple\src\compiler_rust\target\bootstrap.generations\.rejected.9d12f4f0...20550.0\deps\libspl_hosted_runtime-d33a4d50eeeb8dfd.rlib'
$ echo ${#P}
268
```

MSYS reaches the file because it issues its own wide-character/long-path calls.
The Stage-3 materialized consumer opens by Win32 path without the `\\?\`
prefix (and without relying on the per-process long-path opt-in), so the open
fails and the audit — correctly fail-closed — refuses to proceed.

The length comes from the quarantine name itself, generated in
`scripts/check/lib/bootstrap-authority-generation-publish.pl`'s `$quarantine`
handler:

```perl
my $candidate=".rejected.$final_leaf.$$.$attempt";
```

`$final_leaf` is already `<64 hex>-<64 hex>` (129 chars), so the quarantine
directory name is ~138 chars before any content path is appended. A generation
directory that audits fine becomes unauditable purely by being quarantined —
the rename that is supposed to park a bad generation safely is what breaks the
next run.

## Why this is self-perpetuating

Quarantine happens on a FAILED publish. The failure that produced it here was
the unprivileged-symlink defect
(`bootstrap_publish_blocked_windows_native_symlink_privilege_2026-09-07.md`).
So the first failure leaves behind an artifact that makes every later attempt
fail differently, with an error that points at a "missing" file rather than at
the length limit — costing a second investigation. Nothing in the bootstrap
cleans `.rejected.*` up, and nothing warns that its presence is fatal.

## Workaround (what unblocked this host)

Delete the quarantined directory once the real generation is committed. Verify
first that the committed generation is NOT the quarantined one:

```
$ grep '^generation=' src/compiler_rust/target/bootstrap.current.env
generation=d602b9ff2d5a5f2f6eefaeb8...        # != .rejected.9d12f4f0...
$ chmod -R u+w '<.rejected dir>' && rm -rf '<.rejected dir>'
```

This is a workaround, not a fix: the next failed publish recreates the trap.

## Proposed fix (owner's call; nothing changed here)

1. **Long-path-correct opens in the consumer** — the general fix. Open through
   `\\?\`-prefixed paths (or enable the long-path manifest/opt-in) wherever it
   walks the authority tree, so a legal NTFS path is never misreported as
   `ERROR_PATH_NOT_FOUND`. This also removes a whole class of future
   deep-path failures, not just this one.
2. **Shorten the quarantine leaf** — e.g. `.rejected.<first 16 of hash>.<pid>.<n>`,
   or park quarantines in a sibling directory with a short name. Cheap, but only
   buys headroom; it does not make the consumer long-path-correct.
3. **Make the consumer's error name the real cause** — an `ERROR_PATH_NOT_FOUND`
   on a path longer than 260 characters should say so. The current message sent
   this investigation looking for a deleted file.

Recommend 1 plus 3; 2 is a reasonable belt-and-braces addition.

## Related

- `bootstrap_publish_blocked_windows_native_symlink_privilege_2026-09-07.md` —
  the failure that created this quarantine.
- `bootstrap_windows_abi_default_ignores_host_triple_2026-09-24.md` —
  `SIMPLE_WINDOWS_ABI=gnu` is required on this host for an unrelated reason.

## Re-checked against `origin/main` after the 2026-09-25 long-path work

`main` landed `fix(scv/admission): … Windows long paths` (55ec3a44daf) and
related Windows Stage-2 commits, so this record was re-verified rather than
assumed to still apply. **It still applies.**

The new `\?\` handling lives in path validation/normalization helpers —
`authority.shs` lines 4098, 4104 and 4180 all *check* that a resolved path is in
extended `\?\C:\...` form:

```csharp
if (!p.StartsWith(@"\?\") || p.Length < 7 || p[5] != ':' || p[6] != '\' || ...
```

But the function that actually failed here does not prefix anything:

```csharp
static SafeFileHandle Open(string p, bool raw, uint access) {
    var h = CreateFileW(p, access, 1, IntPtr.Zero, 3,
        0x02000000u | (raw ? 0x00200000u : 0), IntPtr.Zero);
    if (h.IsInvalid) { h.Dispose(); throw Error("api.open:" + p); }
```

`Open()` (authority.shs:4022-4025) passes its argument straight to `CreateFileW`,
so a legal NTFS path longer than 260 characters still fails with
`ERROR_PATH_NOT_FOUND` and surfaces as `api.open:<path>:win32=3` — the exact
failure recorded above. Proposed fix 1 (long-path-correct opens in the consumer)
is therefore still open; the validation helpers assume callers already produced
extended-form paths, and this caller does not.

## 2026-09-26: BROADER THAN FILED — a NORMAL published generation is 10 chars from the limit

This record was written from the quarantine symptom (a `.rejected.*` leaf at 268
chars). That framing understates the defect. The quarantine name was not the
cause; it was merely the first path long enough to cross the line.

Measured on a fresh worktree of `origin/main`, the failure reproduced on an
ordinary, successfully published generation — no quarantine involved:

```
stage3-materialized-consumer: Exception calling "Run" with "0" argument(s):
  "api.open:C:\Users\User\dev\simple-phase1-wt\src\compiler_rust\target\bootstrap.generations\
   f7494e6157785f795864fe783303672bfd22b0972e22ba6140c6d5783c50ef64-ae29ae74daa56c999477441834f4b3cc635af99ffdc3113a5608d2c5254fa274\
   deps\libspl_hosted_runtime-1812b80203687942.rlib:win32=3"
ERROR — source, Git state, configuration, seed, or checker changed during preflight
```

Note the reported verdict blames "source, Git state, configuration, seed, or
checker changed during preflight". That is misleading: nothing changed. The
audit simply could not open a file, twice, and the surrounding logic attributes
an unreadable path to a concurrent mutation. This wording cost real
investigation time and is worth fixing on its own.

Path lengths, measured:

| location | length | margin to 260 |
|---|---|---|
| worktree `C:\Users\User\dev\simple-phase1-wt\...` | **260** | **0 — fails** |
| main checkout `C:\Users\User\dev\simple\...` | 250 | **10** |
| short worktree `C:\p1\...` | 231 | 29 |

The generation leaf is structurally long and fixed: `bootstrap.generations\` +
`<64 hex>-<64 hex>` (129) + `\deps\libspl_hosted_runtime-<16 hex>.rlib`, i.e.
**~176 characters below the repo root before any checkout path**. So:

**Any checkout whose path is ~10 characters longer than
`C:\Users\User\dev\simple` cannot complete a bootstrap on Windows.** The
existing checkout works by a 10-character accident. `C:\Users\Developer\dev\simple`
(+5), `C:\Users\User\dev\simple-main` (+5), or a CI agent workspace such as
`C:\actions-runner\_work\simple\simple` would all fail, on a clean tree, with no
quarantine present — and the failure would be reported as a spurious
"changed during preflight".

This makes proposed fix 1 (long-path-correct `Open()`) not a hardening nicety
but a prerequisite for Windows bootstrap on any path that is not already short.
Shortening the quarantine leaf (proposed fix 2) does **not** address this case at
all, since no quarantine is involved.

Workaround, verified: run the bootstrap from a short checkout path. `C:\p1`
buys 29 characters of headroom and got past this point.

## 2026-10-11: Reproduced at a 3-char root (`C:\q`); retained `stage2-home` dirs and `noop-v1` generation receipts fail later-run audits at ANY root

Host: Windows 11 dev host, Git Bash, worktree at `C:\q` (3-char root,
`x86_64-pc-windows-msvc`), wrapper lane
`bootstrap-windows.sh --strategy=adhoc --incremental-unlimited --full-bootstrap
--stop-after-stage2 --output=build/bootstrap`.

A FIRST run in a clean `C:\q` tree passed every materialized-consumer audit and
admitted Stage 2. Every defect below was measured on the SECOND and later runs,
with paths measured from the wrapper's own error text and `find | awk` length
counts (MSYS reaches these files; the consumer cannot).

1. **Re-run retention defeats any root.** Each run renames the prior
   `stage2-home` to `stage2-home.working-attempt-<UTC>-<pid>` (+41 chars over
   the 11-char final leaf; bootstrap-from-scratch.sh ~line 3485). A populated
   home contains
   `.cache\simple\v1\projects\<64 hex>\native-build\noop-v1\<64 hex>\generations\<64 hex>.receipt`:
   measured **323 chars at `C:\q` with the final leaf** and **363 chars
   retained** — over `MAX_PATH` at any root. The next run's `git-state-before`
   consumer walk dies in plain .NET `Directory.EnumerateFileSystemEntries`
   ("could not find part of the path", the 280-char `noop-v1\<64 hex>`
   DIRECTORY) inside `AuditTree` (authority.shs ~line 4989). Consequence: on
   Windows the lane is currently **single-shot per clean tree** — the first run
   audits before these directories exist; every later run fails before any
   stage starts until a human deletes the retained homes.

2. **`Open()` is long-path-correct now; directories are not.** Current
   `authority.shs` `Open()` calls `CreateFileW(NativePath(p), …)` (~line 4417),
   so 277-char FILE paths are tolerated — e.g.
   `bootstrap.generations\<64>-<64>\deps\libspl_hosted_runtime-<64 hex>.rlib`,
   which the wrapper's content-hash "freezing" of package outputs produces
   (16-hex cargo suffixes only appear in older/direct cargo builds). A first
   run coexists with those files fine. The remaining failure class is .NET
   DIRECTORY APIs (`EnumerateFileSystemEntries`, `Directory.CreateDirectory`)
   on directories deeper than 260 chars. Proposed fix 1 should be scoped
   accordingly: `\?\`-prefix directory enumeration/creation (or the
   manifest/opt-in), not just file opens.

3. **Verified workaround (this host, twice):** before each run,
   `rm -rf build/bootstrap/stage3/<platform>/stage2-home*` (mutable working
   state only — receipts, snapshots and admitted dirs are untouched and the
   audit still binds them). With homes purged, a re-run passes the consumer
   walk. Not a fix: it destroys wrapper-retained state and must be repeated
   before every run.

Adjacent observation (not this defect): Stage-2 `native-build` output is not
byte-reproducible run-over-run with a warm module cache — "rebuilt 2" modules
change `simple.exe`'s sha256 each run (observed `82ffe1fd…`, `a11aba47…`,
`0dcd79a5…`). The differing binaries perform identical manual smoke work in
~8 s, so the delta appears to be embedded build metadata, not codegen.
Recorded here so the next investigator does not re-derive it; split into its
own record if it ever gates admission.
