# Derived helper runtime is distinct from the product runtime

The manager policy changes include native C code. A newer SPL source snapshot
does not update an older runtime archive. Manager support images therefore
accept an explicit `--helper-runtime-receipt` only with derived helper source.
The producer admission is replayed unchanged; product compilation continues to
use its original runtime authority. Only support-image compilation selects the
separately verified helper provider.

The `simple-derived-helper-runtime-v1` receipt binds target, native build source
commit/tree and input inventory, an exact provider directory inventory, tool snapshot,
and capability receipt. The archive route uses runtime bundle `auto`.
Verification rejects missing/changed/unlisted provider files and symlinks.
The `simple-helper-runtime-capability-v1` receipt must bind the same source,
provider inventory and tools and carry actual zero-work-deadline, finite-cleanup
and memory-monitor evidence. Receipt validation never creates that evidence.
The native inventory covers compiler_rust, runtime, counterpart C SDK and backend
plugin ABI headers. Complete membership is checked against the build commit and
every byte is replayed against the helper checkout. A later SPL/script-only
helper commit is allowed only when those native inputs remain identical. Its
full SPL source snapshot remains independently bound by the image receipt.
The current tracked and nonignored untracked native input membership must also
equal the build snapshot, so newly added native inputs cannot evade comparison.
Capability evidence additionally pins the actual probe executable, a link
receipt with the exact fresh native-all archive in its input inventory, and
an execution receipt with compile/run exits and quiescence. A source-only C
test or a symbol-presence audit is insufficient to publish this qualification.

The existing canonical Cargo construction is retained for the provider:
`cargo build --locked --offline --manifest-path src/compiler_rust/Cargo.toml
--profile bootstrap --target x86_64-pc-windows-msvc -p simple-native-all
-p spl_hosted_runtime`, with the same reviewed LLVM feature arguments and
Windows compiler/SDK environment as Phase2. This is runtime construction, not
a Rust-seed replacement for production tests. The runtime owner alone writes
the private provider projection/cache and freezes the final helper source pin.
Its immutable output and actual capability results are prerequisites for the
qualified receipt. Earlier direct-C tests may not be relabeled archive tests.
On Windows, the managed owner is the SPL WinJob implementation; generic POSIX
V4 symbol presence is not a capability proof. Qualification must execute the
changed Windows owner fixture linked with this provider, along with applicable
bounded-runner deadline/cleanup checks. Unsupported V4 stubs never count as PASS.

The executable shell contract fixture passed three evolving checks, stopping
after the final cycle. It uses deliberately non-executable test archive bytes:
valid binding, missing fields, extra provider, changed archive, changed/new
native inputs and altered link evidence. It establishes verifier behavior only.
No actual archive capability,
manager startup or product deployment is claimed by this source change.
