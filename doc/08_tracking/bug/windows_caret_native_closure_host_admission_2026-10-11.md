# Windows Caret closure gate rejects the host before compilation

Status: FIX PREPARED; owner: tool_build_plan; 2026-10-11.

The production detect_host_target function returned exit 1 on
MSYS_NT-10.0-26300 / x86_64. It supported Linux, Darwin and FreeBSD only.
Evidence: build/windows-phase4-logs/caret-host-admission-corrected.txt in the
Windows Phase4 checkout. The prior PATH-deficient probe is not valid evidence.

The isolated contracts repair adds Windows triples through the shared host
helper, validates GNU/MSVC ABI spelling, adds .exe suffixes and native paths,
and permits SIMPLE_CARET_ARTIFACT_ROOT for isolated output and cache storage.
The exact target is now supplied to native-build. Windows symbol inspection
uses llvm-readobj --coff-imports and requires valid COFF-format output: nm -u
alone can report an empty table on stripped PE while DLL imports remain.
Existing forbidden Caret ABI checks, explicit simple-core archive requirement,
runtime hash and bootstrap/seed rejection remain enforced.

Focused contract validation: scripts/check/check-llm-caret-native-closure-host.shs
checks host/ABI selection, output suffixes, checker argument boundaries and
malformed/empty/failing checker rejection, plus forbidden PE/Unix ABI symbols.
This is harness verification only; it does not manufacture a product receipt.

Independent review also found inherited fail-open checks: grep errors could be
treated as no forbidden symbol/seed banner, and a failed hasher could yield an
empty identity through its awk pipeline. The repair distinguishes grep absence
from read/checker errors, preserves hasher exit status and requires 64 hex digest
characters. Changed-helper tests passed for clean, forbidden, missing-input,
failed-hasher and malformed-digest cases; shell syntax and diff checks passed.

Remaining: execute the repaired closure gate with a qualified Windows Phase4
compiler and matching pure simple-core archive, then run real Caret CLI and cs
dashboard behavior. Terminal/PTY/thread runtime support remains unverified.
