# Stage4 admitted no compiler-backfill capsule

**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

## Symptom

The pure-Simple strict linker derived final runtime requests and staged runtime
providers, but it never discovered or inventoried the dedicated compiler
backfill. Ordinary `libsimple_native_all.a` discovery also ran before the strict
branch and relied on a later rejection.

## Fix and prevention

Strict Stage4 bypasses native-all discovery and treats the exact Cargo archive
under `SIMPLE_RUNTIME_PATH` as read-only input. After final request derivation,
it builds a transaction-owned Linux ELF or macOS Mach-O capsule before staging
the capability providers.

Pure-Simple derives the sorted `rt_cranelift_*` manifest from the Rust-parity
two/three-field `nm` form, performs the relocatable closure link, localizes all
other globals, strips constructor/destructor sections, and creates a
deterministic one-member archive. Portable tool discovery covers configured,
Homebrew LLVM/LLVM 18, versioned LLVM, and GNU `objcopy` forms.

Final inventory rejects invalid envelopes, changed global symbol tables, and
canonical overlap with the localized runtime-native owner plus all five staged
capability providers. Transitive requested-owner resolution now runs,
while exact projected-capsule linking remains fail-closed. All failure paths
clean the owned transaction; the raw input is never copied, modified, or
deleted. Projected linking and executable proof remain open. No compiler, native,
runtime, C, Cargo, or Simple execution is claimed under this session's
static-only restriction.

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule C: filed before 2026-07-29, no runnable repro in the record, no status line existed); closed as stale per the "too old / not valid -> close" triage policy. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification if reopened.
