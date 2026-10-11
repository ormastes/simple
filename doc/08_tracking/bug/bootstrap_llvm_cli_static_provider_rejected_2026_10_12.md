# Bootstrap rejects a static LLVM authority for the explicit CLI backend

Status: focused provider contract repaired; actual Linux CI bootstrap remains
unqualified pending a new causally required run. Other native platforms unexecuted.

## Observed boundary and version policy

Run38169694975, job114559519792, immutable source
27b236a51c20dbb43765740c05d8d94d45f36a7e installed the authenticated official
LLVM23.1.1 archive (SHA832aeb58d105de1cabc7b982dd2c65de0610f7377df48ae8fc2dd8e97420a15c).
The exact LLVM/Rust/C-tool pin passed, then Cargo seed/native_all passed. Pure
Simple bootstrap exited1 at preflight: admitted LLVM23.1.1 not found.

This is NOT a 23.1.1-versus23.1.2 policy conflict. `_llvm23_version_admitted`
accepts23.1.1 first; native Linux/FreeBSD additionally admit23.1.2. No version
pin is changed. Cargo's non-Windows Inkwell uses llvm23-1-force-static, whereas
the shared detector previously accepted a prefix only if a recognized shared
library filename existed. The installer/pin validate static archives/tools.

Full job log retained `/mnt/c/Temp/simple-linux-latest-failure-20261012/job-full.log`.
It contains no archive library inventory. We do not claim that the archive has
no shared library, nor identify a missing shared basename. The proven mismatch
is that shared-library detection is unnecessarily required by explicit CLI mode.

## Actual backend routing

At exact27b236a:
- driver_aot_native_output.spl3840 calls compile_module_with_backend_target_cpu_storage_bindings.
- backend_helpers.spl416 selects Llvm for explicit `llvm`; the independent
  `llvm-lib` branch selects LlvmLib. Around510 it checks llc versus libLLVM
  independently. Around520 the bootstrap Llvm route calls
  llvm_compile_module_direct_compiled.
- llvm_codegen_adapter.spl160-178 translates MIR and calls compile_ir_to_object.
- llvm_backend_tools.spl148 implements IR-to-object with the llc CLI.
- llvm_lib_backend.spl imports std.sffi.llvm; llvm_loader.spl loads DynLib and
  remains a shared-provider requirement.

Candidate base59fbd8d7a406b66976be6ddaf34974fa29166fd8 has unchanged shared
detection relative to failed27b236a. The diagnostic installer is not in that
release ancestry; no unrelated installer/workflow commits are included here.

## Narrow repair

Bootstrap chooses `LLVM_PROVIDER_REQUIREMENT=static-cli` only for native
Linux/FreeBSD with explicit backend `llvm`. Other backends/hosts select shared.
The detector preserves shared lookup priority/default and admits a static
fallback only for the matching native host/target and LLVM23. It requires:

- llvm-config's prefix and libdir belong exactly to the selected authority;
- executable llc, llvm-as, opt, clang, clang++, llvm-ar with exact matching version;
- a nonempty llvm-config --link-static --libnames list, only archive basenames;
- every reported archive plus Polly/PollyISL exists, is nonempty, and is readable
  by the selected llvm-ar with at least one actual archive member.

The result is explicitly tagged LLVM_PROVIDER_KIND=static-cli, with no LLVM_LIB
or fabricated SIMPLE_LLVM_PATH. CLI tools and Rust static prefix share the same
selected authority. Shared mode and llvm-lib still reject a static-only prefix.
No provider alias, symbol suppression, patch-version relaxation or seed fallback.

## Focused execution and limits

`test/01_unit/scripts/bootstrap_llvm_static_cli_provider_test.shs` executes the
actual detector and production bootstrap selection block with controlled tool
fixtures and real archive containers. The original detector fails the static
acceptance case. Candidate cycle1 passed24 checks; cycle2 adds llvm-config prefix
identity rejection and passes25. Root review found that an empty valid archive still passed ar t;
cycle3 requires nonempty member output and passes26 checks, including that
negative. The three-cycle limit is reached. Existing bootstrap_llvm23_platform_detection
shared/version-policy suite passes once. Shell syntax and diff checks pass.
Artifacts: `/mnt/c/Temp/simple-llvm-static-cli-admission-20261012`.

Positive cases: native Linux/FreeBSD, prefix containing spaces, shared priority.
Negative cases: defaultshared/llvm-lib, unknown mode, Darwin/Windows/SimpleOS,
missing/corrupt/empty-valid archive, missing Polly, empty/traversal archive names, foreign
prefix/libdir, unadmitted patch, mismatched/missing CLI tools. Simulated hosts are
shell policy tests, not native platform qualification. Archives contain test data;
these fixtures establish admission logic, not a working LLVM installation.

No full build restarted, no installation download, no compiler performance or
memory improvement claimed. Detection is startup-only; it retains no long-lived
allocation/cache. Actual immutable-asset CLI invocation and complete bootstrap
remain the next integration gate. Windows/macOS/BSD/SimpleOS execution unqualified.

A separate real installed-provider check calls the actual static helper on
`/usr/lib/llvm-23`, llvm-config23.1.2, without hiding/removing its shared library.
It passes with provider=static-cli and empty LLVM_LIB. `/usr/bin/time -v` records
1.52seconds elapsed and74184KiB maximum child/process RSS. This bounds the
startup validation cost on this installed provider, not compiler memory or CI
asset23.1.1 availability. Receipts: local-static-owner.log and
local-static-owner-time.txt. No unchanged shared-policy test was rerun.
