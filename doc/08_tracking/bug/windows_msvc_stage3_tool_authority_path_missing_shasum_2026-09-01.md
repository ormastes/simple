# Windows MSVC bootstrap lane aborts binding tool authority: PATH lacks `shasum`

**Date:** 2026-09-01
**Status:** Root-caused and fixed (environment fix landed); Stage 2 admission still open
**Lane:** `x86_64-pc-windows-msvc`, output dir `build/cx1`
**Failing gate:** the Stage 3 provenance step that must run before Stage 2 is
built — `bootstrap-from-scratch.sh:2351` `bootstrap_stage3_tool_authority_snapshot`,
whose failure prints `error: could not bind bootstrap tool authority` and exits 1.

## Ground truth at the time of filing

No Windows Stage 2 has ever been admitted, on either ABI lane:

- `find build -name admission.env -o -name stage2-admitted -type d` returns **nothing**.
- `find build bootstrap -name '*.rejected'` returns **nothing** — the `.rejected`
  artifact cited by an earlier report no longer exists in this tree.
- `build/cx1/stage3/x86_64-pc-windows-msvc/runtime-admitted.txt` and
  `build/bootstrap/stage3/x86_64-pc-windows-gnu/runtime-admitted.txt` are
  **runtime-authority** snapshots, not Stage 2 admission receipts. They must not
  be quoted as evidence of admission.
- `WindowsBootstrapReceiptV1`, required by §4 of
  `doc/03_plan/compiler/windows_bootstrap_separate_hosts_nonconflicting_plan_2026-08-30.md`,
  is **unimplemented**: the only two occurrences in the tree are in that plan
  document itself (lines 72 and 180), whose status is "Proposed". The artifact
  the sanctioned pipeline actually writes is
  `<output>/stage3/<platform>/stage2-admitted/admission.env`
  (`bootstrap-from-scratch.sh:2142-2143`). Until the V1 schema is implemented,
  `admission.env` is the only receipt that can exist.

## Root cause

`bootstrap_stage3_tool_authority_snapshot`
(`scripts/check/lib/bootstrap-stage3/authority.shs:736`) iterates a fixed tool
list: `cargo rustc <cc> clang ld ar ranlib sh env perl sed file shasum openssl`.
Every unresolvable tool is a hard `return 1`.

The Sep-1 run (pid 22183, 17:07-17:09) left
`build/cx1/stage3/x86_64-pc-windows-msvc/tool-authority-before.txt.tmp.22183`,
56 lines, whose last record is `tool=file` — i.e. it died on the **next** entry,
`shasum`. Line 1 of that tmp records the run's PATH:

```
PATH=/mingw64/bin:/usr/bin:<npm/codex/CUDA/Windows dirs>
```

On this host `shasum` is `/usr/bin/core_perl/shasum` (MSYS2 core_perl), and
`/usr/bin/core_perl` is absent from that PATH. Reproduced directly:

```
$ env PATH=/mingw64/bin:/usr/bin:/c/WINDOWS/system32 sh -c 'command -v shasum || echo SHASUM_MISSING'
SHASUM_MISSING
```

The same PATH also omitted every MSVC tool directory (`cl.exe`, `link.exe`,
`lib.exe` all unresolvable) and `/usr/local/bin`. This is a launch-environment
defect, not a compiler or script defect: `scripts/bootstrap/bootstrap-windows.sh`
deliberately does not set up an MSVC environment, it inherits the caller's.

**Second, independent failure mode found while fixing the first.** The same
function rejects any PATH component that is not an existing, already-canonical
directory (`[ -d "$dir" ] || return 1`, plus a `pwd -P` equality test). An
inherited Windows PATH routinely carries missing and non-canonical entries; with
`shasum` fixed but the raw PATH passed through, the snapshot still returned 1
during path enumeration, after only 10 lines.

## Fix

New Windows-only file `scripts/setup/windows-msvc-bootstrap-env.shs`, to be
sourced before the bootstrap. It prepends the MSVC/SDK/MSYS tool dirs and
`/usr/bin/core_perl`, sets `INCLUDE`/`LIB`, filters the PATH down to existing
canonical unique absolute components, and points `TMPDIR`/`TMP`/`TEMP` at `/d/`
(C: is at 100%, 23G free of 2.3T; D: has ~797G free).

**Cross-platform impact: none.** The file is new and Windows-only; it is sourced
by nothing on Unix and no existing script was modified. Unix branches are
byte-identical.

## Verification

```
$ sh -c '. scripts/setup/windows-msvc-bootstrap-env.shs
         . scripts/check/lib/bootstrap-stage3/authority.shs
         bootstrap_stage3_tool_authority_snapshot "$OUT" "$PATH" "$(pwd -P)"
         echo "REPO_ENV_SNAPSHOT_RC=$?"'
REPO_ENV_SNAPSHOT_RC=0
$ grep -c '^tool=' "$OUT"
14
```

Seed identity at verification time: `src/compiler_rust/target/release/simple.exe`
== `deps/simple.exe` (FRESH), 39,120,896 bytes, md5 `286f66b8615dce0e0da788f0550c4008`.

## Unblock condition

Stage 2 admission (`stage2-admitted/admission.env`) can now be attempted. Two
known remaining risks, neither addressed here:

1. **Lock contention** — a concurrent `cargo`/`rustc` was live in
   `src/compiler_rust/target` during this investigation; `bootstrap_acquire_rust_authority`
   contends with it. This is what failed the ADMIT13 run.
2. **`WindowsBootstrapReceiptV1` is unimplemented**, so §4 of the plan cannot be
   satisfied by any run today. Either implement the schema or amend the plan to
   name `admission.env` as the Windows receipt of record.

## Follow-on blockers found by actually running the lane (2026-09-01)

Fixing the PATH let the run reach the sanctioned pipeline, which then failed
twice more. Both are recorded here because each one on its own reproduces as a
different-looking failure and would otherwise be re-diagnosed from scratch.

### Blocker 2 — the reason-receipt gate (not a defect; the documented route)

`sh scripts/bootstrap/bootstrap-windows.sh --msvc --stop-after-stage2 --output=...`
exits **64** with:

```
bootstrap-policy-error: reason-receipt-required; run 'simple run src/app/build/bootstrap_receipt_main.spl --bootstrap-reason=<typed-reason> --bootstrap-receipt=<path> ...'
```

`bootstrap-from-scratch.sh:410-417` carves out the correct route for this exact
situation: `--stop-after-stage2` **together with** `--full-bootstrap` and no
receipt sets `bootstrap_stage2_trust_root=1` with
`bootstrap_reason=stage2-trust-root-refresh`, because "the first independently
admitted pure-Simple parent cannot itself require a receipt produced by that
parent." Since no Windows Stage 2 has ever been admitted, this lane is that
trust root. The correct command is therefore:

```
sh scripts/bootstrap/bootstrap-windows.sh --msvc --full-bootstrap \
   --stop-after-stage2 --output=/d/simple_build/bootstrap-msvc
```

Success verdict for that command is the literal line
`Stage 2 admitted; stopping before Stage 3 as requested.` with exit 0, and it is
emitted only after `[ -x "${stage2_admitted_bin}" ]` passes
(`bootstrap-from-scratch.sh:2756-2762`).

### Blocker 3 — LLVM not found

```
error: LLVM not found (shared platform detection: scripts/setup/platform-detect.shs, versions: 18)
```

`platform-detect.shs` looks for an `llvm-config` reporting major 18; this host's
first `llvm-config` on PATH is MSYS2's, reporting 21.1.1, and the Windows
well-known-prefix list (`_llvm_prefixes`) covers only `%ProgramFiles%/LLVM`.
Fixed by exporting the supported version-named override
`LLVM_SYS_180_PREFIX=/c/dev/install/clang+llvm-18.1.8-x86_64-pc-windows-msvc`
(`platform-detect.shs:136`). Verified `LLVM_FOUND=1 LLVM_VERSION=18`.

### Blocker 4 — MinGW headers fed to `cl.exe` (ABI mixing)

```
error: rust-seed-build failed with exit 101
error: failed to run custom build command for `llvm-sys v180.0.0`
```

`llvm-sys`'s build script runs the **first `llvm-config` on PATH** and passes its
`--cflags` to cc-rs. With MSYS2/mingw64 ahead of the MSVC LLVM install those
cflags are `-IC:/dev/tool/msys2/mingw64/include`, so `cl.exe` was handed MinGW
headers:

```
cl.exe -nologo -MD -O1 -Brepro -IC:/dev/tool/msys2/mingw64/include ... wrappers/target.c
C:/dev/tool/msys2/mingw64/include\stdlib.h(389): error C2085: '_exit': ...
C:/dev/tool/msys2/mingw64/include\stdlib.h(729): error C2085: 'lldiv_t': ...
C:/dev/tool/msys2/mingw64/include\malloc.h(128): error C2065: '_ALLOCA_S_MARKER_SIZE': ...
```

Setting `LLVM_SYS_180_PREFIX` alone is **not** sufficient — PATH order decides
which `llvm-config` the build script runs. The env script now places
`clang+llvm-18.1.8-x86_64-pc-windows-msvc/bin` ahead of the MinGW bin dir, so
`llvm-config`, `clang` and `lld-link` are all MSVC-ABI. `ar`/`ranlib`/`ld`/
`file`/`openssl` still come from MinGW; they are host utilities, not ABI
producers, and the Stage 3 tool-authority snapshot records them either way.

**Locale note for whoever reads these logs next:** MSVC diagnostics on this host
are Korean. Grep for the codes (`error C2085`, `error C2143`, `LNK\d+`), never
for English words — an English grep returns zero on a log full of hard errors.
