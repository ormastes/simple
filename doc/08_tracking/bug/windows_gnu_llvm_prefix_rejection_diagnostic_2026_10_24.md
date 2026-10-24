# Windows GNU LLVM prefix rejection hides its ABI requirement

Status: diagnostic repaired; GNU bootstrap qualification remains pending.

On release/1.0.0 at `a26b26f3197`, the configured Windows LLVM root is
`/c/dev/tool/clang+llvm-23.1.1-x86_64-pc-windows-msvc`. The actual host prefix
contains `bin/LLVM-C.dll` and lacks `lib/libLLVM-23.dll.a`.

The Windows GNU detector validates the LLVM version and then requires the
MinGW import library. Previously it silently rejected a prefix missing that
library, leaving callers to report only that admitted LLVM was not found.
This conceals the difference between an absent version and an incompatible
provider layout, and can mislead diagnosis toward environment propagation.

The detector already reads `SIMPLE_HOST_LLVM_ROOT`, then invokes
`host-env.shs --get llvm_root` when that value is absent. These observations
do not prove that an environment scrub caused the configured prefix to be
lost. The configured MSVC prefix is insufficient for the GNU lane even when
the detector receives it successfully.

The repair retains detection behavior and emits a missing-import-library
diagnostic only when no compatible provider is found. A valid later fallback
remains silent. It does not admit an MSVC DLL for GNU builds, manufacture an
import library, or claim the GNU seed/Phase 3/Phase 4 passes.

Validation: `bash scripts/check/check-windows-llvm-prefix-diagnostic.shs`
passed under native Git Bash on 2026-10-24. The fixture sources the complete
production detector with isolated providers and checks four cases: a matching
version with missing GNU import library, a compatible GNU fallback, a valid
MSVC prefix, and a wrong-version negative control. Prefixes contain spaces.
