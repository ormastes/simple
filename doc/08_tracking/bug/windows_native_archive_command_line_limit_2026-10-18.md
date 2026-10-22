# Windows native archive object list exceeds CreateProcess limit

Status: fixed at the Rust bootstrap archive boundary; focused real-tool controls PASS.
Full bootstrap qualification remains separate.

## Reproduction and cause

The frozen `67d20f767430e06d7699fa6cfdb87dfbd12eb3f1` Windows diagnostic
successfully compiled its three missing units and retained all 1,364 objects.
Its `--emit-archive` operation then failed with:

`Build failed: run archive tool llvm-ar: The filename or extension is too long. (os error 206)`

Original evidence is retained under
`D:/dev/simple-phase2-codec-repair-20261018/build/record-key-contract/native-method461-diag-native/analysis.md`.
The diagnostic used the canonical LLVM/MSVC environment, a 5,859,375 KiB RSS
cap and a finite 900-second timeout; it completed with native exit 1 and a
quiescent process tree. This archive failure is distinct from the earlier
executable-build exit 134.

`NativeProjectBuilder::archive_objects` passed every object directly to
`Command::output`, exceeding Windows' command-line limit. The executable-link
owner already batches archive inputs; the direct archive owner bypassed it.

## Repair and scope

The std-only `native_project/archive.rs` owns the existing archive command
forms and the direct archive execution helper. On Windows, the latter writes
an invocation-private object response file and waits for the archive process
before its caller removes the temporary directory. LLVM-ar explicitly selects
`--rsp-quoting=posix` and reuses the executable linker's POSIX path quoting;
LLVM-lib uses Windows response quoting. Newline-bearing paths are rejected.
Archive operation flags, exit-status handling and executable-link batching
are unchanged. See the [LLVM response-file documentation](https://www.llvm.org/docs/CommandGuide/llvm-ar.html).

Pure-Simple stage-4 archive capsules in
`src/compiler/70.backend/backend/llvm_native_link_stage4_archives.spl` archive
one localized object per call using the existing `io_runtime.process_run`
facade. They do not have this unbounded argv and need no host-access change.
This repair is Rust bootstrap plumbing; it does not change the normal
Pure-Simple tool selection policy.

## Focused controls (Windows x86_64 MSVC, LLVM 23.1.1)

The std-only harness imports the exact production module, including its
permanent `archive_tests.rs` tests. The real-tool test is explicitly ignored
in ordinary unit runs and fails if required fixture/tool variables are absent.
For this qualification it was included, not skipped.

- A real `clang-cl` COFF object was copied into 1,000 separately named inputs
  under paths containing spaces, accented text and Korean text. Each copy has
  a distinct valid COFF timestamp, making its complete bytes distinguishable.
- The direct production command builder reproduced native OS error 206 with
  **124,000 UTF-16 units** of object arguments (greater than 32,767).
- The production `create_archive` helper succeeded with both LLVM-ar and
  LLVM-lib. Each archive contained exactly the 1,000 expected member names,
  and all extracted member bytes matched the respective input.
- Quoting, newline rejection and existing GNU/MSVC command forms also passed.
- Terminal result: **4 passed, 0 failed, 0 ignored**, 0.82 seconds. Guard:
  complete, native exit 0, quiescent 1, peak RSS 24,468 KiB; enforced cap
  5,859,375 KiB and timeout 120 seconds.

The first control attempt passed LLVM-ar but exposed an incorrect test
assumption that LLVM-lib preserves basename-only member names and order.
LLVM-lib uses full names and can reorder members; the corrected test checks
the exact basename inventory and every extracted payload. Both attempts and
the compiled fixture remain in the ignored evidence directory.

Evidence: `D:/dev/simple-windows-archive-rsp-20261018/build/archive-rsp-controls/`
(`run.sh`, `harness.rs`, `tests.log`, `guard.receipt`, fixture, archives,
extracted members and provenance manifest).
Test executable SHA-256:
`b6ef529a760ab325cbca8dfb9c24907edf0d3e856497a97205b23617c434effc`.

No whole-crate Cargo build or full bootstrap was run for this focused repair.
