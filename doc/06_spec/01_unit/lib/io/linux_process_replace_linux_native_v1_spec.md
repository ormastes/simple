# Actual Linux replacement ownership specimens — R2

Authored manual for
`test/01_unit/lib/io/linux_process_replace_linux_native_v1_spec.spl`.
All3 cases NOT_RUN. No native/compiler/link/bootstrap execution was attempted.

Prerequisites: admitted dedicated native LP64 little-endian x86_64/AArch64 test
process, genuine current main-thread procfs origin, actual executable ELF64 for
THAT ISA, its real SHA256/exact bytes, independent trusted fixture directory and
a DISTINCT second directory. Environment fixture metadata:
SIMPLE_REPLACE_FIXTURE_ELF, SIMPLE_REPLACE_FIXTURE_SHA256,
SIMPLE_REPLACE_FIXTURE_BYTES, SIMPLE_REPLACE_FIXTURE_DIRECTORY,
SIMPLE_REPLACE_FIXTURE_OTHER_DIRECTORY. Max512MiB. Missing setup fails; no skip,
unsupported-platform fake pass or externally supplied native receipt exists.
Administrator must provision actual memory/time for the full memfd and bounded
scratch/native arrays. These metadata strings are not Host budget/grant proof.
Do not run inside a process with live descendant/Git leases or create new
CLONE_FILES/VM/sighand sharing during preparation.

1. Use the actual scoped producer and actual source fd, <=64KiB copy turns,
  0500/all4 real seals, matching ELF/machine/header validation and sealed-fd hash.
   Require ready/no exec, copy opaque owner and close once. Copied close/prepare
   must return canonical closed tombstone without another native close or cwd
   handback. Original caller cwd was returned IMMEDIATELY at open and remains
   independently cleanup-capable; private duplicate is closed internally.
2. Deliberately change expected digest for an actual valid source. Require
   actual sealed-byte comparison failure with opaque owner retained, no exec,
   cleanup pending and sticky first error. Later replace refuses before effects;
   close retains the original mismatch and does not return original cwd again.
3. Open actual producer but stop BEFORE copying/hashing. Observe the private
   duplicate's real identity. Close the caller's actual borrowed original through
   an old value copy, then open a distinct actual directory, allowing fd reuse.
   Complete bounded preparation and require private-held identity remains the
   original. This demonstrates actual independent native custody after old-copy
   close; it does not fake an exec or inspect raw caller fd integers.

All loops have finite40000-turn bounds and assert terminal ready/failure. Actual
partial native writes can exhaust this finite budget; that is failure, never
invented completion. Global fixture slots reject new admission while previous
owner/cwd cleanup is pending. after_each never overwrites a retained carrier.
No replacement is invoked in the test runner; the mismatch replace call is an
actual production refusal before any exec path.

NOT_COVERED: real same-process exec success/failure, argv/env delivery, unchanged
Host workload/deadline, real CLONE_FILES peer isolation, real separate-TGID
VM/sighand refusal before handler mutation, source/write/signal/cwd/close fault
injection, nonstdio close-on-exec and stdio preservation. Dedicated-process
acceptance remains in detail design, NOT_RUN; source/architecture ACK is not
native compatibility, AgentReady or resource-settlement evidence.
