# Stage4 admitted no compiler-backfill capsule

## Symptom

The pure-Simple strict linker derived final runtime requests and staged runtime
providers, but it never discovered or inventoried the dedicated compiler
backfill. Ordinary `libsimple_native_all.a` discovery also ran before the strict
branch and relied on a later rejection.

## Fix and prevention

Strict Stage4 now bypasses native-all discovery and inventories the exact
compiler-backfill basename from `SIMPLE_RUNTIME_PATH` before runtime, entry, or
provider temporaries exist. Linux ELF and macOS Mach-O are the only admitted
producer formats. A pure-Simple validator rejects empty or repeated globals,
non-`rt_cranelift_*` definitions, the two excluded compatibility wrappers, and
undefined `rt_*`/`spl_*` dependencies.

The inventory is read-only and deliberately does not select or link the
archive. The Cargo artifact is still an unlocalized source staticlib and is
expected to fail closed; deterministic one-member localization remains open.
No compiler, native, runtime, C, Cargo, or Simple execution is claimed under
this session's static-only restriction.

The next pure-Simple slice now derives the sorted compiler export manifest and
the raw symbols to localize directly from portable `nm` text. It mirrors the
Rust producer's exact two/three-field row parser and rejects duplicate exports
or runtime ownership outside the manifest. Tool orchestration and executable
proof remain pending.

Portable pure-Simple tool discovery now also resolves `SIMPLE_OBJCOPY`,
Homebrew LLVM/LLVM 18, versioned LLVM tools, and GNU `objcopy` in that order.

The strict linker now uses those pieces to build a transaction-owned localized
capsule: relocatable closure link, raw-symbol localization, constructor section
removal, deterministic one-member archive creation, final inventory, and
fail-closed cleanup. The raw Cargo archive remains read-only. Exact full symbol
table equality and overlap checks against the staged providers remain open.
