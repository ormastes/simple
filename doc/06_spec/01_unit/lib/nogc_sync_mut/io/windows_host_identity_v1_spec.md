# Windows host identity observation v1

Status: **NOT_RUN**. Authored source review and executable specifications do not
establish Win32 ABI, linker, runtime, registry or native host qualification.
No compiler, build or test command was run for this change.

Source: `src/lib/nogc_sync_mut/io/windows_host_identity_v1.spl`.
Specification: `test/01_unit/lib/nogc_sync_mut/io/windows_host_identity_v1_spec.spl`.
Native fixture: `test/fixtures/bootstrap_builder/windows_host_identity_v1_main.spl`.

## Contract and limits

The read-only native observer queries the explicit 64-bit HKLM registry view.
`MachineGuid` must be exactly REG_SZ with 36 ASCII GUID characters plus a NUL
(74 bytes). The canonical result is installation identity, with a versioned
prefix; cloned or restored installations and privileged tampering can reuse it.
It is not proof of a physical device or authenticated OS integrity.

The documented PrefetchParameters `BootId` must be REG_DWORD with exactly four
bytes, greater than zero and below 0xffffffff. Missing, inaccessible, malformed,
zero and exhausted values are errors. The returned field is `boot_counter`,
with `boot_assurance = "successful-boot-counter"`. **It is not a globally unique
boot incarnation or a continuity credential.** A successful-boot counter can
repeat after rollback, restoration, reinstallation, wrap or privileged edits;
rejecting boundary values cannot detect a wrap that already happened. Failed
boots and other restarts need not yield distinct counters. Equality must never
admit host adoption, journal continuity, generation reuse or receipt reuse.
A separate fresh service incarnation and startup quarantine are required at the
service boundary; this leaf does not implement those policies.

The architecture comes from GetNativeSystemInfo and must agree with the native
machine reported by IsWow64Process2. Unknown, x86 and disagreement fail closed.
This supports native x64/ARM64 AOT execution on Windows 10/Server version 1709+
only. Interpreter and JIT callers are refused before direct Win32 calls; other
platforms return an explicit error. One 512-byte zeroed heap allocation owns all
Win32 buffers; fixed bounds constrain all writes and reads. HeapFree is checked
on all postallocation exits. No shell, environment, configuration, PID, uptime
or wall clock contributes identity.

## Authored scenarios

1. Normalize canonical uppercase hexadecimal GUIDs.
2. Reject wrong registry type/byte count, missing storage/terminator, nil GUID,
   embedded NUL, malformed separators, nonhex and nonASCII units.
3. Admit the bounded positive DWORD range; reject wrong type/width, zero,
   negative and exhausted/overflow counters.
4. Admit matching x64/ARM64 native architecture; reject emulation disagreement
   and unsupported/unknown architecture.

Native follow-up, NOT_RUN: link the fixture with Advapi32.lib and Kernel32.lib
through the admitted Windows AOT path and run without printing identities.
Observe identical machine identity/counter within one successful boot, and
record successful-boot counter behavior across an actual successful reboot.
These observations establish only the declared lower-assurance counter contract.
On interpreter/JIT and non-Windows, require explicit refusal. Registry denial
and abnormal query types need isolated controlled fixtures, not modification of
live OS identity keys. Allocation cleanup and native import availability remain
unqualified until observed with the exact producer/runtime/provider.

## Primary evidence

- [RegGetValueW](https://learn.microsoft.com/en-us/windows/win32/api/winreg/nf-winreg-reggetvaluew):
  exact ABI, registry type restrictions, byte count including NUL, explicit
  64-bit registry view, zero-on-failure and error behavior.
- [Memory integrity enablement](https://learn.microsoft.com/en-us/windows-hardware/design/device-experiences/oem-hvci-enablement):
  BootId registry path and successful-boot counter semantics.
- [GetNativeSystemInfo](https://learn.microsoft.com/en-us/windows/win32/api/sysinfoapi/nf-sysinfoapi-getnativesysteminfo):
  native SYSTEM_INFO query and emulation caveat.
- [SYSTEM_INFO](https://learn.microsoft.com/en-us/windows/win32/api/sysinfoapi/ns-sysinfoapi-system_info):
  wProcessorArchitecture layout and architecture values.
- [IsWow64Process2](https://learn.microsoft.com/en-us/windows/win32/api/wow64apiset/nf-wow64apiset-iswow64process2):
  native-machine output, failure handling and minimum supported version.
- [Image file machine constants](https://learn.microsoft.com/en-us/windows/win32/sysinfo/image-file-machine-constants):
  AMD64/ARM64 machine values.

The NtQueryInformationProcess telemetry BootId and
SYSTEM_BOOT_ENVIRONMENT_INFORMATION BootIdentifier are not used. No unsupported
claim about boot GUID uniqueness is inferred from names or opaque fields.
