# Windows install, deploy, and antivirus handling (2026-09-24)

This guide covers a Windows developer host that builds Simple from source, and
what a downloaded Simple release means for end users. It records the state on
2026-09-24. Items marked **intended** or **unverified** are not current, proven
behaviour.

Related guides:
[windows_c_compiler_authority_lint.md](windows_c_compiler_authority_lint.md),
[llvm_23_deploy_2026-08-21.md](llvm_23_deploy_2026-08-21.md),
[../../tooling/windows_phase2_runtime_capsule.md](../../tooling/windows_phase2_runtime_capsule.md).

## 0. First: build on a trusted Dev Drive, and measure before excluding

### Check for a Dev Drive

Do this before adding any exclusions. From an elevated prompt, run:

```powershell
fsutil devdrv query D:
```

On the reference host, D: is a 1.1 TB ReFS volume, and the query returned:

```
This is a trusted developer volume.
No filters are currently attached to this developer volume.
Developer volumes are enabled.
```

When a Dev Drive is trusted and has no filter attached, antivirus does not
scan it at all. A Defender path exclusion for anything on that volume adds
nothing.

**Recommendation:** keep the checkout and build on a trusted Dev Drive. Use the
exclusions in section 2 only for output that has to live on a normal volume.

A Dev Drive needs Windows 11 build 22621.2338 or later, at least 50 GB, and
admin rights to create. On a trusted Dev Drive, Defender uses its asynchronous
performance mode. Third-party antivirus attaches to Dev Drives by default (see
section 3). Do not detach filters with `fsutil devdrv setfiltersallowed`,
because that removes protection.

### Find out what Defender is actually scanning

Defender includes a profiler. Use it as the first diagnostic when
"Antimalware Service Executable" (MsMpEng) is busy. Both commands need admin:

```powershell
New-MpPerformanceRecording -RecordTo C:\path\outside\checkout\defender.etl -Seconds 30
Get-MpPerformanceReport -Path C:\path\outside\checkout\defender.etl -TopProcesses 10 -TopFiles 10 -TopExtensions 10
```

The recording lasts 30 seconds. Keep the `.etl` file outside any checkout.

Measured on the reference host, 2026-09-24, over 30 s. MsMpEng was using about
1.7 cores and about 900 MB, and **no** scheduled scan was running:

| Process | Scan time | Files | What was scanned |
|---|---|---|---|
| `grep.exe` | 27.3 s | 2,847 | Almost all `.spl` sources in the C: checkout |
| `git.exe` | 2.5 s | 28,487 | Nearly all `.idx` pack indexes in that repo's `.git` |
| `claude.exe` | 1.5 s | — | Agent transcript `.jsonl` files |

**Conclusion:** the dominant Defender cost was a recursive grep over a source
tree on a normal (C:) volume. The source tree is deliberately **not** excluded,
and should not be. The fix is to work from a checkout on a Dev Drive, not to
exclude the sources.

## 1. Install and bootstrap on a Windows developer host

### Toolchain policy

Simple is clang-only (2026-09-24). On Windows the C compiler is `clang-cl`.
Do not use `cl`, `gcc`, or `g++`. The linker is `lld-link`, because mold has no
PE/COFF backend. There is one exception: `link.exe` is still the sanctioned
linker for Rust's MSVC target, which the seed build uses. See
`.claude/rules/code-style.md` § Toolchain policy.

### Checkout

1. Clone, then materialize symlinks:
   `sh scripts/setup/materialize-symlinks-windows.shs`.
2. After materializing, never run `git add -A` or `jj commit -a` in that
   checkout. The materialized files show up as changes, and a whole-tree commit
   would replace the symlinks in the repository. Always commit named paths.

### Environment

Source the MSVC lane environment in the same shell (Git Bash / MSYS2) that runs
the bootstrap:

```sh
. scripts/setup/windows-msvc-bootstrap-env.shs
```

The script assumes these host-specific paths. It checks that each one exists
and stops with `missing PATH component: <dir>` if one is missing:

- Visual Studio 2022 Community, MSVC `14.44.35207`. Only its headers,
  libraries, and `link.exe` are used, not `cl`.
- Windows SDK `10.0.26100.0`.
- MSYS2 at `/c/dev/tool/msys2`.
- LLVM `23.1.1` at `/c/dev/tool/clang+llvm-23.1.1-x86_64-pc-windows-msvc`.

The only override is `LLVM_SYS_231_PREFIX` (or `SIMPLE_LLVM_WIN_ROOT_23`). It
must be set before sourcing the script. The Visual Studio, SDK, and MSYS2 paths
are fixed. A host with other versions has to edit the script.

The script also filters `PATH` down to absolute, existing, canonical
directories. It does this because the Stage 3 tool-authority snapshot fails
closed on any PATH entry that is not one of those.

### Entry command

```sh
sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2
```

A plain `--full-bootstrap` stops at the receipt gate. `--stop-after-stage2` is
the way in for a trust-root run. The header comment of
`windows-msvc-bootstrap-env.shs` still names `bootstrap-windows.sh --msvc`.
That comment is stale. The command above is the one verified on 2026-09-24.
`bin/simple build bootstrap` is a separate Rust-side check and is not the
sanctioned bootstrap (see CLAUDE.md).

### Fixes landed 2026-09-24 that this path depends on

- **#1457:** `llvm-toolchain-env.shs` exports `LLVM_CONFIG` in drive-letter
  form (`C:/...`). `canonical_native_command` accepted only paths that start
  with `/`, so it rejected that value. The Rust seed fingerprint then aborted
  with no diagnostic: `failed to fingerprint Rust seed inputs` /
  `ABORTED: stage=fingerprint exit=1`. The fix converts the path with
  `cygpath -u` first.
- **#1459:** the seed failed to compile under `--features llvm` (E0599, no
  `left` on `inkwell::values::ValueKind`). Every full bootstrap aborted at
  `stage=rust-rust-seed-build exit=101`. The fix uses inkwell 0.9's
  `ValueKind::basic()`.
- **#1461:** `windows-msvc-bootstrap-env.shs` exports `VCToolsInstallDir`.
  `scripts/check/check-bootstrap-preflight.shs` finds the Rust MSVC-target
  `link.exe` through this variable. Without it, preflight fails before any
  pure-Simple stage starts.
- **#1460 and #1462:** Microsoft Defender exclusions for build output
  (section 2).

### Do not run the bootstrap as Administrator

Nothing in the bootstrap needs elevation. Only the Defender registration in
section 2 is elevated, through a single UAC prompt of its own. Run the
bootstrap from a normal, non-elevated shell.

### Pitfalls found the hard way

- **Do not add files to a checkout while its bootstrap preflight is running.**
  Preflight snapshots the state of source, Git, configuration, seed, and
  checker. If any of it changes, preflight aborts with
  `ERROR — source, Git state, configuration, seed, or checker changed during preflight`.
- **Keep bootstrap logs outside the checkout.** Redirecting logs into the tree
  is a file change of this kind.
- **The Stage 2 refusal before execution is not caused by Defender. Its cause
  is still open.** The symptom is
  `log was NEVER CREATED ... wrapper PRECONDITION refusal ... UNDIAGNOSABLE`,
  with a wall time of about 220 s. It reproduced identically on 2026-09-24
  under two conditions: with every stage compiler process-excluded, and on the
  unfiltered trusted Dev Drive. That rules Defender out.

## 2. Microsoft Defender exclusions (developer host)

Defender real-time protection scans every file the compiler writes and every
binary it launches. A bootstrap writes tens of thousands of objects, and each
freshly built, unsigned `simple.exe` is scanned again whenever it runs.

```sh
sh scripts/setup/windows-defender-exclusions.shs list     # print the plan, change nothing
sh scripts/setup/windows-defender-exclusions.shs add      # add, then verify
sh scripts/setup/windows-defender-exclusions.shs remove   # remove exactly this set, then verify
```

The last line of stdout is the verdict:

- `PASS — <n> exclusion(s) verified present|absent` (exit 0)
- `FAIL — ...` (exit 1)
- `ERROR — nothing was checked` (exit 2)

Cost: 2–3 `powershell.exe` starts (~0.5 s each). The bounded process
discovery adds about 1 s, and a `list` run takes about 2.5 s. This is one-time
setup and is not on any build or push path.

### Scope

**Version note.** The first version (#1460) covered only `build/`,
`.simple/storage/build/`, `src/compiler_rust/target/`, `bin/release/`, and any
deployed `bin/release/*/simple*.exe` as processes. It did **not** cover the
bootstrap's Stage 1/2/3 compilers. #1462 (current `main`) replaced that list.
It resolves the scope from the storage roots
(`scripts/lib/storage-roots.shs`; the bootstrap writes through
`scripts/bootstrap/lib/centralized-storage.shs`) instead of listing directories
by hand. If it cannot resolve those roots, it stops with `ERROR` (exit 2).

If the checkout is on a trusted, unfiltered Dev Drive (section 0), the entries
on that volume are redundant, because the volume is not scanned. The entry that
still matters is the user storage cache, which normally lives on C:.

Path exclusions:

- `<checkout>/build`
- `<checkout>/.simple/storage`, the whole worktree storage root. It holds the
  bootstrap stage compilers, native caches, and the bootstrap `tmp/`, `test/`,
  and `evidence/` roots.
- `<user storage>/cache/compiler`, which holds the compiler `bootstrap/` and
  `native-build/` caches. On the reference host this is
  `C:\Users\ormas\.cache\simple\storage\cache\compiler`.
- `<checkout>/src/compiler_rust/target`
- `<checkout>/bin/release`

Process exclusions:

- The stage compilers, at their expected paths, even before they exist. They
  are created partway through the bootstrap:
  `<worktree storage>/build/bootstrap/stage2/<platform>/simple.exe`,
  `.../stage3/<platform>/simple.exe`, and
  `.../stage3/<platform>/stage2-runtime-authority/simple.exe`.
- Deployed `bin/release/*/simple*.exe`, if present.
- Any `simple*.exe` found by one bounded `find -maxdepth 5` under the bootstrap
  root.

A path exclusion stops Defender from scanning files **in** that directory. A
process exclusion stops it from scanning files the process **opens**. For a
stage compiler, those are the thousands of source files it reads. Path
exclusions alone do not cover that. This is why #1462 adds the stage
compilers as processes.

Kept out of scope on purpose: the source tree stays scanned. The scope must
never be widened to a drive root, a whole user profile, or a download
directory. The one user-level entry is a single named cache subdirectory. The
trade-off is that anything dropped into an excluded path is not scanned
either, so the set is limited to output that the build recreates from source.

### Behaviour

- The paths come from the script's own location. Running the script from a
  worktree therefore covers that worktree, not the main clone. Run it once per
  checkout.
- Only the Defender call is elevated, through one UAC prompt. If you decline
  the prompt, nothing changes. Verified: the run prints `FAIL — add not applied`.
- The script checks the result by reading `Get-MpPreference` back. It does not
  trust the return of `Add-MpPreference`.
- **The change takes effect as soon as it is registered.** No reboot or
  restart is needed. Path exclusions apply to new file activity immediately,
  so a bootstrap that is already running benefits. Treat process exclusions as
  starting from the next launch of that process.
- Deployed binaries that appear after `add` are not covered until you run
  `add` again. Run it again after the first deploy. `remove` removes only the
  set it computes at the time you run it.

Verified counts on the reference host (2026-09-24):

| Checkout | Version | Result |
|---|---|---|
| `C:/Users/ormas/dev/simple` | #1460 | 6 exclusions |
| `D:/wk-bootstrap-20260924` | #1460 | 4 (no deployed binaries yet) |
| `D:/wk-bootstrap-20260924` | #1462 | `PASS — 8 exclusion(s) verified present` (5 paths + 3 processes) |

### Which antivirus is active?

The script handles **Microsoft Defender only**. It does not check which
antivirus product is active. Nothing in the repo detects or configures
third-party antivirus today. To see what is registered, run:

```powershell
Get-CimInstance -Namespace root/SecurityCenter2 -ClassName AntiVirusProduct |
  Select-Object displayName, productState
```

This query is cheap and does not scan anything. `SecurityCenter2` does not
exist on Windows Server SKUs. Only `Windows Defender` was checked with it
(productState 397568 on the reference host). Third-party display names are
**unverified**. Match a case-insensitive substring such as `*ESET*` or
`*AhnLab*`, not an exact string.

**Windows Security Center alone is not enough.** On the reference host,
`C:\Program Files\AhnLab\Safe Transaction` is installed, and it appears in
Defender's own performance report (section 0). Even so, the `SecurityCenter2`
query above lists only Windows Defender. AhnLab Safe Transaction is a
banking-security product, not a registered antivirus, but the point holds:
software that hooks file activity may not be registered with Security Center.
Also check the well-known install directories, for example
`C:\Program Files\AhnLab\`, `C:\Program Files\ESET\`, and
`C:\Program Files (x86)\ESTsoft\`. Only the AhnLab directory was observed; the
other directory names are **unverified**. Check them with a directory listing,
not a drive-wide search.

## 3. Third-party antivirus

Source: research carried out on 2026-09-24. **Caveat on method:** every vendor
fact below comes from web-search extracts of the cited vendor pages. No vendor
page was read in full. Check the exact syntax against the vendor page before
scripting anything. None of the commands below has been run in this repo.

**Microsoft Defender is the only product that can be automated through a
supported path** (`Add-MpPreference`, section 2). The rest:

| Product | Local CLI for an exclusion | What the owner or admin must do first |
|---|---|---|
| ESET (home and Endpoint) | `ecmd /setcfg <xml>` imports a **whole** configuration, not a delta. | Enable ESET CMD. With password mode, sign the XML with `xmlsigntool`. The exclusion XML node name is **unverified**. |
| Kaspersky Endpoint Security | `avp.com IMPORT <file> /password=…` imports a **whole** settings file. There is no per-exclusion verb. | Enable password protection. The syntax comes from a non-vendor KB. Trusted-zone export/import as a CLI is **unverified**. |
| Bitdefender GravityZone (BEST) | `product.console.exe` through the Power User module. | The console admin must enable Power User and set its password. The exact on-access antimalware verb is **unverified**. |
| AhnLab V3 Lite, V3 365 Clinic, V3 IS 9.0 | None documented. | GUI: 환경 설정 > 검사 예외 설정. Managed: AhnLab Policy Center, which overrides local edits. |
| ALYac (ESTsecurity) | None documented. | GUI: 환경설정 > 탐지 제외 > 추가. The Enterprise console policy steps are **unverified**. |
| Norton 360 | None documented. | GUI only. The current menu path comes from a KB extract. The older "Scans and Risks" path is **unverified**. |
| McAfee consumer | None documented. | GUI: Real-Time Scanning > Excluded Files. |
| Trellix ENS (Windows) | None found. The exclusion CLI is Linux ENS only. | Trellix ePO On-Access Scan policy. |
| Avast / AVG | None documented. | GUI (Settings > General > Exceptions) or Business Hub policy. |
| Trend Micro | None documented. | GUI (Exception Lists) or an Apex One / Apex Central policy. |
| Sophos Central / Intercept X | None. `SEDcli.exe` only toggles Tamper Protection. | Sophos Central policy or Global Exclusions. Sophos Home detail is **unverified**. |
| Naver Vaccine (PC) | Discontinued 2023-11-30. The source is news coverage, not a vendor page. | — |

Rules:

- Never bypass tamper protection or self-protection to add an exclusion. For
  example, do not use `SEDcli.exe` to turn protection off.
- Do not recommend `fsutil devdrv setfiltersallowed`. Detaching antivirus
  filters from a Dev Drive removes protection.
- On a managed machine, the exclusion belongs in the vendor console policy and
  is the admin's decision.

For false positives, use each vendor's web submission form. Two email routes
came from non-vendor aggregators and are **unverified**: AhnLab
`v3sos@ahnlab.com` / `samples@ahnlab.com`, and ALYac `esrc@estsecurity.com`.

### Dev Drive with third-party antivirus

Third-party antivirus filters attach to Dev Drives by default, and performance
mode is a Defender-only feature. On a machine running V3, Norton, or another
product, a Dev Drive still gives the ReFS and filesystem gains but not the
asynchronous-scan benefit. `fsutil devdrv query <drive>` shows whether any
filter is attached (section 0).

## 4. End users (downloaded releases)

- **An installer must not silently add antivirus exclusions.** Malware does
  this, and Defender may flag an installer that does it. If an installer ever
  offers `windows-defender-exclusions.shs`, it must ask first and must offer
  `remove`. This is **intended** policy. No Simple installer does this today.
- **Code signing does not exempt files from on-access scanning, and it does
  not speed up builds.** It gives downloaded releases a stable publisher
  identity. That helps with SmartScreen prompts and false-positive handling,
  and a false positive fixed once tends to stay fixed. A locally built
  `simple.exe` is unsigned in any case.
- Options (prices and eligibility are from search extracts and should be
  re-checked):
  - SignPath Foundation: free OV-level signing for OSI-licensed open source
    with no proprietary components, used from CI.
  - Azure Artifact Signing (formerly Trusted Signing): Basic plan about
    $9.99/month.
  - Since 2024 (the EV OIDs were removed in August 2024), an EV certificate no
    longer skips SmartScreen reputation. OV and EV now build reputation the
    same way.
- Windows release signing in CI is **intended**, not current: no workflow in
  `.github/workflows/` signs a Windows binary as of this date.
