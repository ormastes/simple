# Linker specs were never checked on Windows in CI (2026-09-19)

## Status

Partially closed. The Windows job now exists and is proven fail-closed on
Linux; the Windows half of the proof lands the first time the job runs on a PR.

## What was broken

Every fix to the pure-Simple mold-like linker (`src/compiler/70.backend/linker/**`,
`src/lib/common/linker/**`) was proven on Linux only.

- `.github/workflows/windows-tests.yml` has three Windows jobs. None of them
  executes a Simple spec. `windows-x64` and `windows-arm64` print
  `⚠ Native Windows binary not yet available` and exit 0; the `linker-tests`
  job is `runs-on: ubuntu-latest` and every one of its steps is
  `continue-on-error: true`. Its `summary` job explicitly states "Windows tests
  are informational".
- `.github/workflows/windows-build.yml` did build a real seed `simple.exe` on
  `windows-latest` for both MSVC and MinGW, but only ever called
  `native-build`. It ran no spec.
- `cross-platform.yml` and `rust-bootstrap-multiplatform.yml` cover cargo/seed
  builds, not spec execution.

So a Windows-only linker regression — a path separator, a text-mode read
corrupting fixture bytes, a CRLF in a linker script, a case-insensitive fixture
collision — could land green.

## What was fixed

`scripts/check/check-linker-specs-portable.shs` runs the 19 host-independent
linker specs and is invoked by a new `Linker specs (Windows)` step in
`windows-build.yml`, on both matrix legs, before Stage 2. `windows-build.yml`
also gained a `pull_request:` trigger (it had only `push:`, so it never
appeared as a PR check) and linker paths in both filters.

A real coverage gap was found and closed while proving the guard red: deleting
the `ch == "\r"` arm of `_ld_is_whitespace`
(`src/compiler/70.backend/linker/linker_script.spl:67`) left all 51
pre-existing `linker_script_spec` examples GREEN. CRLF tolerance in the
linker-script tokenizer — the single most likely Windows-specific linker defect
— was untested. Three cases were added (CRLF script equivalent to its LF form,
a lone `\r` as inter-token whitespace, a `//` comment terminated by CRLF), in
both `test/01_unit/` and `test/unit/` mirrors. With the `\r` arm removed the
guard is `FAIL`; with it restored, `PASS`.

## Verified by run (Linux, aarch64, Rust seed `simple` v1.0.0-beta.12)

- all 27 specs under `test/01_unit/compiler/backend/linker/` and
  `test/01_unit/lib/common/linker/` pass; the 19 portable ones run in ~18s
- `--selftest` PASS (3 fixtures)
- full scan `PASS - 19 spec(s) executed, 314 example(s) passed, 0 failed`
- `--binary /nonexistent/simple` -> `ERROR` exit 2
- CR-arm removed -> `FAIL` exit 1 naming `linker_script_spec.spl`
- workflow YAML parses; 9 push paths, 9 pull_request paths, matrix intact
- `check-guard-wiring.shs` PASS, `guard_unwired_new=0`

## Verified by reasoning only — NOT run on Windows

No Windows machine was available. These will only be proven when the job runs:

1. **The seed can interpret a spec on Windows at all.** No Windows job has ever
   done this. `simple.exe` is proven to run `--version` and `native-build`;
   `"$SEED" <spec>.spl` is not. If spec interpretation itself is broken on
   Windows the new job goes red on all 19 — which is the correct outcome, but
   it is a different defect from a linker bug.
2. **Repo-relative forward-slash fixture paths.** `test/fixtures/linker/elf/...`
   is passed to `file_read_bytes`. Win32 accepts `/`, and the Rust seed's file
   I/O goes through `std::fs` (no text mode), so byte reads should be exact —
   but this is inference from the API, not a measurement.
3. **Binary fixtures survive checkout.** `.gitattributes` has a repo-wide
   `* text=auto eol=lf` and no explicit `-text` for `.o`/`.a`/`.so.1`.
   `git check-attr` confirms `text: auto`, and git's auto-detection treats
   NUL-bearing content as binary, which ELF objects are from byte 4. Judged
   safe; if a fixture ever arrives CRLF-mangled on a Windows runner, the
   parse specs fail loudly rather than silently, and the fix is an explicit
   `test/fixtures/linker/** -text -diff` rule.
4. **No case-insensitive fixture collision.** Checked mechanically
   (`ls ... | tr A-Z a-z | sort | uniq -d`) over
   `test/fixtures/linker/{elf,corpus}` — none. NTFS is case-insensitive, so a
   collision would have silently dropped a fixture.
5. **No Windows-specific defect found in the linker source itself.** Searched
   `src/compiler/70.backend/linker/**` and `src/lib/common/linker/**` for
   `split("\n")`, `splitlines`, `lines()`, hardcoded `"/"` path joins and
   backslash handling: no hits. `_ld_is_whitespace` already accepted `\r`
   (untested until now — see above). This is a static finding; a real Windows
   run may still surface something.

## Excluded specs — by name, with reason

Eight of the 27 cannot run on Windows. They are excluded by name in the guard,
never globbed-and-tolerated.

| spec | reason |
|---|---|
| `elf_dynamic_link_spec.spl` | reads host glibc from `/usr/lib/aarch64-linux-gnu` |
| `elf_gnu_hash_spec.spl` | same |
| `elf_symtab_spec.spl` | same |
| `elf_x64_dynamic_spec.spl` | host `/lib64/ld-linux-x86-64.so.2` interp contract |
| `link_engine_external_spec.spl` | links against host CRT, then EXECUTES the ELF ("hi from libc") |
| `native_linking_internal_spec.spl` | same; also writes to `/tmp` |
| `link_corpus_recipe_spec.spl` | `process_run("sh", ...)` over a POSIX guard script |
| `linker_dead_imports_spec.spl` | `shell()` with POSIX `test`/`grep` |

Verified 2026-09-19: none of the four glibc specs has a `file_exists` or
platform self-skip, so on Windows they would hard-fail on a missing input
rather than reporting a skip. That is precisely why they are excluded by name
instead of being allowed to run.

## Follow-ups

- Promote to the `push,` tier of `config/check/must_check_gates.sdn` only if a
  Linux-side pre-push run of these 19 specs is wanted; the Windows coverage
  this record is about comes from the workflow, not the push tier.
- `check-test-tree-divergence.shs` is RED on this base for unrelated reasons.
  The `linker_script_spec.spl` mirror pair is already in
  `scripts/check/test_tree_divergence_baseline.txt:313`, and the CRLF cases
  were added to BOTH mirrors, so this change introduces no new divergence and
  does not make a baselined pair identical. Measured with the scoped-delta
  helper rather than asserted, per `.claude/rules/vcs.md`:

  ```
  sh scripts/check/check-test-tree-divergence-delta.shs 7c875a81067 <this sha>
  base verdict: check-test-tree-divergence: FAIL — 3922 diverged vs 965
                baselined (3066 new, 109 fixed-but-still-baselined);
                32 mirror-only (31 unallowlisted, 0 stale-allowlist)
  PASS — 3206 pre-existing offender(s), 0 introduced by this range
  ```

  The pre-existing offender list this step-over is recorded against is the
  3,206-entry list the helper saved to
  `/tmp/test_tree_divergence_preexisting.txt`; it is identical at BASE and at
  NEW ("pre-existing red is identical at BASE and NEW; this range introduces
  nothing"). It is not committed — it is a snapshot of another lane's debt, not
  a product of this change, and it is reproducible byte-for-byte by rerunning
  the command above against base `7c875a81067`.
