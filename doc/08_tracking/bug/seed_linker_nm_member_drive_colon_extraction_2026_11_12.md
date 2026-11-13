# Bug: seed linker parses `nm -A` member names by last colon; CI-baked drive-letter members break the COFF owner-member extraction

Date: 2026-11-12
Lane: work/release-1.0.0-mcp-local (worktree `.build/mcp-release-1.0.0-source`, base f6f190ccc2d)
Host: Windows 11 / Git Bash, x86_64-pc-windows-msvc, 64 GiB RAM
Producer: phase-1 seed (Rust) running the Stage 2 native-build link of `bootstrap_main.spl`

## Symptom

Stage 2 MSVC bootstrap on release/1.0.0 tip f6f190ccc2d compiles all 1,642
modules, then the link fails:

```text
Build failed: owner member \a\rust\rust\build\x86_64-pc-windows-msvc\stage1-std\
x86_64-pc-windows-msvc\dist\build\compiler_builtins/752ee066348396b5\out\
719209a4cb9689f4-negsf2.o was not extracted from
.../stage2-runtime-authority/simple_native_all.lib
```

(see `build/bootstrap/mcp-local/logs/x86_64-pc-windows-msvc/stage2-native-build.log`)

## Root cause (two defects, one per half of the extraction path)

`linker.rs` (`core-c-bootstrap` shared-`rt_*` owner-member pre-extraction,
added 2026-11-12) maps symbols to archive members by parsing `nm -A` output:

1. **Parse**: `parts[0].trim_end_matches(':').rsplit(':').next()` takes
   everything after the LAST colon of the `<archive>:<member>:` prefix token.
   Vendored MSVC rust-std objects carry CI build paths baked into their
   archive member names — `llvm-ar t simple_native_all.lib` shows
   `C:\a\rust\rust\build\...\719209a4cb9689f4-negsf2.o` (95 of 2,092 members
   contain path separators). The rsplit drops the `C:` drive prefix, so
   `llvm-ar x` is asked for `\a\rust\rust\build\...\negsf2.o`, which matches
   no member; llvm-ar still exits 0, and the subsequent
   `extract_dir.join(member).is_file()` check fails the link.
2. **Extraction check**: even with the correct name, `llvm-ar x` cannot
   materialize a member whose name is not a usable relative path — it
   sanitizes it to its basename. Measured 2026-11-12 on this host:
   extracting `C:\a\rust\rust\build\...\719209a4cb9689f4-negsf2.o` writes
   `./719209a4cb9689f4-negsf2.o` (exit 0), so the joined-path existence check
   alone would still fail.

## Fix

`src/compiler_rust/compiler/src/pipeline/native_project/linker.rs`:

- Build the expected `nm -A` prefix from the exact archive argument passed to
  nm (`external_tool_path(runtime_lib)`) and `strip_prefix` it, falling back
  to the old colon split; member names containing `:` now survive.
- After `llvm-ar x`, fall back to the member's basename component when the
  joined path is not a file, so sanitized drive-letter members resolve.
- Write the extracted owner objects into a clang response file
  (`@native_all_owner_members.rsp`, verbatim `\\?\` spellings) instead of one
  `cmd.arg` per object: on this host's deep worktree the paths exceed
  MAX_PATH and hundreds of them exceed CreateProcess's 32 KiB command line
  (`os error 206` at `cmd.output()`, observed 2026-11-12 on the rerun after
  the parse fix). `@file` expands inline, so link order is unchanged.
- That was not the whole overflow: the assembled MSVC command line still
  exceeded CreateProcess's 32,767-char cap once every `/INCLUDE:` root and
  path arg was counted (`os error 206` again on the second rerun). When the
  assembled line crosses 28,000 chars the whole argument vector -- `/link`
  group included -- is now swapped into one double-quoted
  `@clang_cl_link_full.rsp` (clang expands `@file` inline; single-quote
  posix rsp quoting is not clang-parseable). The swap logs its char count,
  so the log shows the mechanism firing.
- Two clang-cl 23.1.1 response-file quirks, measured 2026-11-13 with a
  minimal repro, turned out to be the real blockers once the overflow was
  bypassed (both earlier rsp attempts failed with
  "clang-cl: error: no such file or directory: '/WHOLEARCHIVE:...'"):
  1. llvm's response-file tokenizer does NOT split tokens on newlines --
     an interior '\n' is attached to the token, so newline-separated rsp
     lines produce unrecognizable `/OPTION...<LF>` tokens that clang treats
     as input files. Space-separated single-line rsp content links fine.
     Both rsp writers space-join (a trailing newline at EOF is stripped).
  2. Verbatim `\\?\` paths cannot pass through clang-cl response-file
     expansion at all: whether as `/WHOLEARCHIVE:` options or plain input
     objects, clang re-escapes them when forwarding to lld and lld reports
     "could not open '\\\\?\\D:\\...'" (doubled backslashes). The identical
     args on the direct command line work. Fix: plain-spell
     (`external_tool_path`) every arg written to an rsp -- the owner-member
     objects are additionally hard-linked to short flat names
     (`owner_NNNN.o`) because their deep member relpaths exceed MAX_PATH
     once spelled plain. Backslash doubling (`quote_cl_response_arg`)
     remains necessary: clang's tokenizer DOES unescape `\\` inside quotes.

`cargo check -p simple-compiler` clean (only a pre-existing unrelated
warning). Stage 2 rerun with the fix in progress at time of writing.

## Notes

- Only members whose baked-in names carry a drive colon are affected; the 94
  path-separator members without a colon parse and extract correctly.
- The old failure mode this pre-extraction prevents (supplement archive
  winning shared `rt_*` symbols, "rejected invalid array handle") is why the
  extraction must succeed rather than be skipped.
