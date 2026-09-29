# Bootstrap collection native providers

Base: main `6b2afa560166eb4d4c457ed97eea414b36a361d6`.

## Failure and fix

The strict Linux Stage2 attempt compiled all 1062 translation units, then failed
at link with `spl_collection_capture_note_lookup`,
`spl_collection_capture_note_hash_probe`, and `spl_ordered_key_cmp` unresolved.
No Stage2 compiler admission, test matrix, or Stage3/4 receipt was produced.

The frozen Rust native-all archive had none of the eight collection ABI roots.
Core-C defined them, but the seed's narrow mutex supplement did not include
them. Adding these roots to that supplement was rejected: its private core-C
heap registry and string layout do not represent Rust-owned values safely.

The fix gives Rust native-all its own ordered-key implementation and compiles
the existing bounded capture engine through a narrow provider translation unit.
Core-C includes the same private header. The provider macro prevents duplicate
exports in unconfigured pure-C source inventories. Both the canonical source
fingerprint and Cargo rebuild inputs include the new C/header dependencies.

The first capture execution on each host passed two of five tests. Three real
failures exposed a further ABI mismatch: Rust strings have bounded bytes with
an explicit length, without a trailing NUL; `rt_interp_cstr` exposes those bytes.
The capture engine's C-string operations could read beyond their allocation.

The corrected owner adapter copies bounded string prefixes into separate
caller-owned site and target buffers. It checks registry membership before heap
access, rejects registered nonstrings, and preserves the explicit trusted raw
C-string contract with bytewise reads through the first NUL. It leaves global
string layout and `rt_interp_cstr` unchanged. Disabled events retain the atomic
fast path. Invalid/nonmatching targets remain filtered; an invalid site for a
matching target fails the capture. Embedded NULs retain existing prefix semantics.

## Executed verification

| Host / criterion | Result |
| --- | --- |
| Linux capture ABI, including boundaries and Rust output ownership | 7 passed, 0 failed, 0 ignored |
| Linux ordered-key contracts | 8 passed, 0 failed, 0 ignored |
| Windows capture ABI, same provider source | 7 passed, 0 failed, 0 ignored |
| Windows ordered-key contracts | 8 passed, 0 failed, 0 ignored |
| Actual LLVM native-all archive, bootstrap profile | Build passed; source and archive hashes recorded |
| C capture and ordering selfchecks against fresh core-C and actual Rust native-all | Four executables passed |
| Native-all symbol availability | One definition each: eight public endpoints and text adapter |

Linux used pinned nightly 2026-09-27 and LLVM 23, bootstrap profile,
`--no-default-features`, offline vendored dependencies, and an isolated D-backed
ext4 Cargo target. Windows used the existing isolated runtime target, bootstrap
profile, `--no-default-features`, offline dependencies, and two jobs. The passing
ordering checks were not repeated. The failed capture logs remain preserved.

Linux evidence: `/mnt/simple-bootstrap-6b2/collections-provider-fix-tests-20260928/cycle2/`
(`capture-owner-abi.log`, `ordering-owner.log`, input hashes and result file).
Windows evidence: `build/mini_builds/collections-providers-review/`
(`windows-ordering-test.*`, `windows-capture-test-cycle2.*`).

Archive/parity evidence: Linux evidence root `native-all/` and `native-all/parity/`.
The native-all build used the prior stopped mutable Cargo target sequentially,
with `--locked --offline --profile bootstrap --target x86_64-unknown-linux-gnu
-p simple-native-all -p spl_hosted_runtime --features llvm`. Its copied archive
is a diagnostic candidate from the dirty fix checkout, not an admitted immutable
generation. The first Rust C-test link omitted LLVM's system libraries and did
not execute; that log is preserved. Remaining Rust links used the pinned
`llvm-config --system-libs --link-static` outputs. Passing core-C checks were
not repeated.

The isolated Windows shared clone's absolute Git alternate paths were not
portable to WSL. A metadata-only setup correction preserves the alternate file
in external evidence. Native Windows Git repacked the fix checkout with two
threads and a 32 MiB window budget, without deleting packs; only the fix
checkout's alternates were cleared after successful completion. Windows and WSL
then read HEAD and the previously unavailable diff object without warnings.
Source object stores and source checkouts remain untouched.

These are focused runtime/provider checks. They do not certify a completed
bootstrap, Stage2 CLI matrix, Stage3, Stage4, or release admission.

## Branch applicability and retained limitations

Root inspected release/1.0 at
`ae0a09389b94d7893c5263f61cfc4e2e2798fee2`: it lacks the collection capture SFFI module
and these endpoint definitions/callers. This feature-specific patch does not
apply to that branch; adding the entire collection feature as a backport is
outside the fix.

Ordered-key text comparisons retain the core-C prefix through the first NUL;
boxed NaN comparisons retain the existing equal result. Follow-up limitations
are recorded separately in the ordered-key contract tracking note.
