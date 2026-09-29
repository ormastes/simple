# Windows hosted C plan binds the environment detector

Status: static diagnosis and narrow source fix; UNVERIFIED at runtime. No
compiler, debugger, native hello or test invocation followed the failed fourth
cycle. Frozen candidate and all its binaries, archives and receipts are intact.

## Actual failure and authority

Candidate `c63bcf6e1a5bc1fb693aec8846d10e0fe71cc486` compiled 1061 modules with
zero failures and linked its Stage 2 compiler. Positional hello compiled its
single source object, then failed before host C-runtime compilation:

`host C runtime/entry compilation unsupported: target
'x86_64-pc-windows-msvc' on host 'x86_64-unknown'`.

The explicit target now reaches the C plan. The host detector remains a
separate input; the plan correctly rejects an unsupported host/target pair.

Rejected image SHA256:
`7b0b7b42f46c3f781df6e64db8ffbdcb2a7e1f5358ace145d7db951b83866618`.
Hello log SHA256:
`fe32fa11ff53c9d5dd881f5fa8277ed4b9f96b851d5b920bba4828e0487af9fc`.
Linked native-all archive SHA256:
`7387116508d74084ed717aa761ec82c4b7659e9f405ae13a4563789ca1ae9007`.

## Confirmed call chain

`llvm_native_link_orchestrator.spl` imports `host_os` and `host_arch` from
`std.platform`. The retained COFF relocations and the actual rejected PE agree:

| Function in the rejected image | Virtual address |
|---|---|
| `llvm_native_link_orchestrator.link_llvm_native` | `0x14073f1a0` |
| `lib.nogc_sync_mut.platform.host_os` | `0x140a80710` |
| `lib.nogc_sync_mut.platform.get_host_os` | `0x140a80220` |
| `lib.nogc_async_mut.env.platform.detect_os` | `0x140a2be40` |

The last two transitions are direct tail jumps. The final detector's image
instructions load `OS` at `0x141340380` and `OSTYPE` at `0x141340390`, matching
the async environment detector. That detector does not call the compiled
runtime platform primitive. With absent environment hints it probes `/bin/sh`
and recognizes Unix uname names; neither an absent shell nor a Windows/MSYS
uname gives it a Windows result.

The shipped `bootstrap_stage_sanity` scrubs all exported environment names
except its owned session/RSS settings, then restores an explicit allowlist.
Neither `OS` nor `OSTYPE` is restored. This is source-bound evidence from the
executed frozen wrapper, not a newly captured process environment snapshot.
The actual hello log confirms that the planner received `unknown`.

The facade's intended sync-source delegation and its compiled binding differ.
The broader module/alias-resolution cause of that difference is not established
by this patch. It is not necessary to invent a broken runtime string ABI or
heap mutation to explain this observed failure.

## Runtime owner and fix

The same rejected image contains the canonical runtime-based chain:

| Function or data | Virtual address |
|---|---|
| `lib.nogc_sync_mut.io_runtime.host_os` | `0x140a7d260` |
| `lib.nogc_sync_mut.sffi.platform.platform_name_raw` | `0x140a94500` |
| linked `rt_platform_name` | `0x140c2e47c` |
| provider's compiled `windows` bytes | `0x14136e91a` |

The provider returns a runtime text value; the canonical host wrapper compares
it through `rt_native_eq` and returns known platform names. It uses uname only
for platforms whose primitive returns a generic name. Linux and macOS retain
their compiled runtime identities; BSD retains the existing uname fallback.
Canonical `host_arch` also handles missing Windows architecture environment
data, as required by the scrubbed bootstrap process.

Fix only the orchestrator's imports: obtain `host_os` and `host_arch` directly
from its existing `std.nogc_sync_mut.io_runtime` owner, matching
`runtime_compiler.spl` and native linking. Remove the unused `is_macos` import.
Do not alter host/target compatibility rules, infer a host from the requested
target, inject OS environment hints, or modify runtime providers.

## Regression and remaining verification

The existing canonical positional hello sanity is the primary regression:
run a newly built producer under the same sanitized Windows environment,
require host C-runtime/entry compilation and link success, then execute the
artifact and require exact `hello` output. The existing
`check-bootstrap-positional-link-contract.shs` also checks explicit selection,
private object cache use, no stubs/delegation and actual execution.

When separately authorized, compare retained new orchestrator relocations to
confirm `io_runtime.host_os`/`host_arch` binding. Linux/macOS bootstrap checks
must retain their normal runtime host results. Compiler/core verification
gates remain pending. Static source and PE analysis are not runtime PASS.

The old raw Rust-owner probe used a different producer/archive and bypassed
`std.platform`; its successful `rt_platform_name -> windows` result never
tested this environment-based C-plan route. The first three diagnostics and
the fourth authorized rebuild cycle remain consumed.
