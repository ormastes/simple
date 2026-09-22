# Phase2 Vulkan scalar/text dynload forwards

Base: `e6ffda6849e6aa7fe01a7d23ddc71e9773286532`. Sidecar S owns only
`runtime_gpu_vulkan_scalar_private.h` and its named fixtures/checker.
The merge owner includes the fragment after the shared loader helpers and
owns the loader/build composition. No registry, required-symbol set, common
helper, compiler or provider implementation changed in this sidecar.

Frozen manifest originally SHA256
`c56264da3bbbeb33286fb86b0b160b012a92006ebd382662c8a86cdfccf5fc5a`;
merge owner authorized subsequent shared/A-interface corrections, ending at
`c82c7448c210276a5633d8e973e359f4069ebe8e834dab81b5b46c164c5b04ef`.
Sidecar S's 29 symbols and signatures did not change.

## Implementation and ownership

23 signed-64 scalar forwards and six C-string forwards preserve canonical
Rust provider signatures and unavailable sentinels. Every call uses an
existing loader lease. Optional `submit_and_wait` retains its own symbol:
the canonical implementation consumes the fence and returns boolean success,
so aliasing the fence-returning operation would change ownership and values.

Each text forward copies before lease release into its own thread-local
4096-byte buffer. Null/unterminated provider output fails closed; invalid
last-error output remains descriptive. Empty provider text remains empty.
Pointers remain valid until the next same-function call on the same thread.
Bounded TLS overhead is 24 KiB/thread, with no per-call heap allocation.

Independent review found that `STATE.strings.clear()` in provider shutdown
can invalidate cached C strings even while the provider lease remains active.
A private blocking mutex now covers each getter-and-copy interval and
shutdown. Registry locks are not held across provider execution. Other scalar
operations remain concurrent. Windows uses SRWLOCK; POSIX uses pthread mutex.
Only macOS was executed in this lane.

## Retained evidence

Evidence root (local, untracked):
`build/evidence/phase2_gpu_vulkan_scalar-c1`, `phase2_gpu_vulkan_scalar-c2`,
and `phase2_gpu_vulkan_scalar-native1` in the isolated sidecar worktree.

The C ABI checker passes all 29 operations using synthetic dynamic providers,
distinct return values, exact argument order/value checks, changed arguments,
missing optional symbols, absent providers, missing required symbols, wrong
ABI, null/unterminated text and text retained after unload. Removing the whole
fragment makes the baseline link fail on the owned symbols.

The concurrent-shutdown fixture coordinates two threads. The provider mutates
its old text during shutdown; guarded copy survives. A mechanically generated
version with the actual production lock sites disabled exits 73 with
`shutdown/text copy race detected`. The unmodified fragment reports
`shutdown/text lifetime PASS`. This is actual guard sensitivity, not a
provider-only negative assertion. Green C rows were not rerun after the later
native-harness-only link corrections.

C1 measured 100,000 bind-buffer forwards in 33.034ms; C2 measured 37.080ms
(about 371ns/call), maximum process RSS 1,622,016 bytes. The same scalar path
was unchanged between these samples; these are absolute observations, not a
claimed latency improvement or statistically established regression result.
The corrected lock adds blocking serialization only to text/shutdown.

The source-only SFFI audit passed four assertions and emitted the backlog.
It is not ABI/provider admission evidence.

## Actual native Simple boundary: blocked by compiler conversion

Producer is admitted Stage2 binary SHA256
`0c65162af9c89bdb9c6583ca91820f795231c9bf4c451b6a69ea66794c66c084`,
under the P0 worktree's `stage3/aarch64-apple-darwin/stage2-admitted/simple`.
Frozen runtime capsule identity:
`99157e8902d570262f1fc59691862b9c3b9d3cbd45373b3127c30df75eb20a6f`.
The exact command is retained in `build/evidence/run-scalar-native.sh`:
strict no-stub fallback, LLVM23 pins, private source/cache/output, one thread,
`native-build --emit-archive --no-mangle --backend cranelift`.

Archive compilation passed, peak sampled tree RSS 61,088 KiB. The native
command entry was the admitted Stage2 binary, but the archive log uses the
Rust native-build driver's output format rather than the pure-Simple frontend
phase trace. No route receipt was captured. The compiler-fix owner identified
the missing Rust `RuntimeFuncSpec` despite membership in the C-string-return
list. Therefore this proves an actual compiled Simple-to-C caller failure,
not independently qualified pure-Simple frontend execution. The route and
source authority require explicit qualification by the compiler/merge owner.
No direct seed invocation occurred in this lane.

The native
harness links the actual compiled `spl_main`, loader fragment, core-C native
runtime and canonical `runtime_legacy_core.c` / `runtime_string_ffi.c`
owners. Initial harness links exposed its missing main bridge and C-string
owner; these were corrected without rebuilding the unchanged Simple archive.

The resulting native executable passes 23 scalar comparisons and the first
three text comparisons, then exits **34** at `rt_vulkan_get_last_error`.
Disassembly of the retained archive proves the conversion mismatch:

- `device_type`: call at 0x50c, then `rt_cstring_to_text` at 0x518.
- `get_last_error`: call at 0x55c, immediately saves raw x0 at 0x560; no conversion.
- `selected_device_driver_identity`: call at 0x5a0, conversion at 0x5ac.

All are declared `-> text` in the same Simple fixture. The C forward returns
the correct C string, established separately by the C ABI checks. Returning a
boxed value here would violate the frozen public ABI and is not an acceptable
repair. Compiler owner `/root/stage2_after_route_fix` has the exact repro and
is responsible for the missing conversion. Native result was guarded, exit
34, peak sampled tree RSS 2,336 KiB, quiescent 1.

Both guards used limit 5,859,375 KiB and reported sampled enforcement;
`hard_memory_limit=0` remains explicit. C2's aggregate script receipt exits 1
because its final native harness link initially lacked main; individual C
mode logs and the race/sabotage logs prove their own results, not an aggregate
native PASS.

**Status:** C boundary and shutdown lifetime regression PASS; actual native
Simple full-boundary qualification BLOCKED by compiler conversion. No GPU
device execution, full runner, compiler matrix, Phase2/3 completion, push or
release is claimed. Independent Astra review required before handoff commit.

Independent Astra-high final review: **PASS** for the scoped C fragment,
ABI signatures, bounded storage, shutdown serialization and retained C
regression evidence; no remaining blocking C-fragment findings. **BLOCKED**
for complete native Simple-boundary qualification, as above. Reviewer:
`/root/stage2_after_capsule_fix/gpu_scalar_review`.
