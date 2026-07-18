# Stage4 admitted no compiler-backfill capsule

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
canonical overlap with all five staged providers. All failure paths clean the
owned transaction; the raw input is never copied, modified, or deleted. Capsule
selection, linking, and executable proof remain open. No compiler, native,
runtime, C, Cargo, or Simple execution is claimed under this session's
static-only restriction.
