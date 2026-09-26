# Windows bootstrap defaults to the MSVC ABI on a host that records, and only has, the GNU lane

Filed: 2026-09-24
Host: DESKTOP-5A4V03J (Windows 11, Git Bash / MSYS2)

## Symptom

`sh scripts/bootstrap/run-phase1-local.shs` — the documented local phase-1
entrypoint — aborts in the first build step:

```
Platform: x86_64-pc-windows-msvc
Building Rust seed compiler + runtime library...
error: rust-seed-build failed with exit 101
VERDICT — ABORTED: stage=rust-rust-seed-build exit=101 signal=none
```

The underlying failure, from
`.simple/storage/build/bootstrap/logs/x86_64-pc-windows-msvc/rust-seed-build.log`:

```
warning: ring@0.17.14: .../vendor/ring/include/ring-core/check.h(27,11):
    fatal error: 'assert.h' file not found
error: failed to run custom build command for `ring v0.17.14`
```

## Cause

`assert.h` is missing because the MSVC CRT and Windows SDK headers are missing,
and they are missing because **this host has no Visual Studio and no Windows SDK
at all**. Verified directly:

```
$ ls -d "/c/Program Files/Microsoft Visual Studio" \
        "/c/Program Files (x86)/Microsoft Visual Studio" \
        "/c/Program Files (x86)/Windows Kits/10/Include"
ls: cannot access ...: No such file or directory   (all three)
$ echo "${INCLUDE:-UNSET}"
UNSET
```

The MSVC lane is therefore not merely misconfigured here — it is unsatisfiable.

Two recorded facts about this host disagree, and nothing reconciles them:

- `config/host/DESKTOP-5A4V03J.sdn` records
  `platform: windows-mingw` and `rustup_host_triple: x86_64-pc-windows-gnu`.
- `scripts/bootstrap/bootstrap-windows.sh:12` hardcodes
  `abi="${SIMPLE_WINDOWS_ABI:-msvc}"`, and
  `scripts/bootstrap/bootstrap-from-scratch.sh:1124-1131` independently forces
  `SIMPLE_WINDOWS_ABI=msvc` on any MINGW/MSYS/CYGWIN host when the variable is
  unset.

`run-phase1-local.shs` *does* source `scripts/setup/host-env.shs`, so
`SIMPLE_HOST_RUSTUP_HOST_TRIPLE=x86_64-pc-windows-gnu` is exported and in scope —
it is simply never consulted when the ABI is chosen. The host config is read and
then ignored for this decision.

## Workaround (verified to change the selected lane)

```
SIMPLE_WINDOWS_ABI=gnu sh scripts/bootstrap/run-phase1-local.shs
```

`--mingw` also works and is recognised anywhere in the argument list
(`bootstrap-windows.sh:15-21` loops over all of `"$@"`).

## Proposed fix

Default the Windows ABI from the host config instead of a hardcoded literal:
add a `windows_abi:` field to `config/host/<hostname>.sdn` (or derive it from
the existing `rustup_host_triple`), export it from `host-env.shs` alongside the
other `SIMPLE_HOST_*` values, and have `bootstrap-windows.sh` and
`bootstrap-from-scratch.sh` prefer it over `msvc`. An explicit
`SIMPLE_WINDOWS_ABI` / `--msvc` / `--mingw` must keep winning over both.

Fail-closed alternative, if a default must stay hardcoded: have the MSVC lane
verify the CRT/SDK headers exist before building, and abort with that as the
stated reason. A missing `assert.h` surfacing from inside a vendored crate's
build script is several layers away from the actual cause and cost this
investigation most of its time.

## Not in scope of this record

Whether the GNU lane completes phase 1 on this host is tracked separately; this
record covers only the ABI selection defect and the unsatisfiable MSVC default.
