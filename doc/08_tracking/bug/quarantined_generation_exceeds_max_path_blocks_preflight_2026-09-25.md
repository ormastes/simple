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
