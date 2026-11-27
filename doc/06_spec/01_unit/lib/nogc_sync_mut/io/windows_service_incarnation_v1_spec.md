# Windows service incarnation nonce v1

Status: **NOT_RUN**. No compiler, build, test, fixture or native invocation was
executed. Authored specifications and source review do not qualify Win32 ABI,
provider availability, native linking or randomness.

Source: `src/lib/nogc_sync_mut/io/windows_service_incarnation_v1.spl`.
Specification: `test/01_unit/lib/nogc_sync_mut/io/windows_service_incarnation_v1_spec.spl`.
Native fixture: `test/fixtures/bootstrap_builder/windows_service_incarnation_v1_main.spl`.

## Contract

`windows_service_incarnation_nonce_v1()` obtains 32 bytes from
`BCryptGenRandom(NULL, buffer, 32, BCRYPT_USE_SYSTEM_PREFERRED_RNG)` and returns
`windows-service-incarnation-v1:` followed by exactly 64 lowercase hexadecimal
characters. Nonzero NTSTATUS, allocation/free failure, or zero sentinel causes
an error. The zero sentinel rejection has negligible false rejection probability
for valid CNG output; it triggers no retry. Interpreter and JIT callers are
refused before raw Win32 calls; other platforms return an explicit error.

One checked 32-byte Win32 heap allocation owns the CNG output. A fixed managed
carrier is allocated before that buffer. Successful CNG bytes are copied within
the exact bound; HeapFree is checked before formatting or returning. CNG failure
still releases the heap buffer. No provider handle is opened for the system RNG.
There is no fallback to clock, uptime, PID, registry, environment, configuration,
sequential numbers or caller data. The deterministic encoder is only a formatting
seam and does not supply entropy or certify ownership.

The persistent service owner calls this once for a fresh service lifetime and
holds its authority separately. Restarting the service requires a fresh nonce.
This value is **service incarnation**, not OS boot identity. Equality and copied
text never establish ownership, adoption, journal continuity or valid scope.
The persistent owner, startup quarantine and scope inventory belong to the
service contract and are not implemented by this entropy leaf. Labels may be
copied in receipts but are not credentials; this API does not prove service
liveness or protect against rollback of caller storage.

## Authored scenarios

1. Exact 32-byte known vector preserves leading zeros and emits canonical hex.
2. High-bit bytes remain unsigned, without sign extension or uppercase output.
3. Empty, short and oversized arrays fail.
4. Zero sentinel fails without a generated default.

Native follow-up, NOT_RUN: link the fixture with Bcrypt.lib and Kernel32.lib
through the admitted Windows AOT producer/runtime, then observe successful
native entropy acquisition without printing its nonce. Source helper vector
assertions cannot prove RNG quality or native ABI correctness. Interpreter/JIT
and non-Windows calls must explicitly refuse. Provider failure and allocation
failure require isolated genuine failure injection; do not replace the CNG
provider or mark simulated formatting vectors as native RNG evidence.

## Primary evidence

[Microsoft BCryptGenRandom reference](https://learn.microsoft.com/en-us/windows/win32/api/bcrypt/nf-bcrypt-bcryptgenrandom)
specifies the NTSTATUS ABI, exact caller buffer size, NULL algorithm with
BCRYPT_USE_SYSTEM_PREFERRED_RNG=0x2, and user-mode Bcrypt.lib/Bcrypt.dll provider.
It documents Windows Vista SP2+ for this flag (Server 2008+); the service owner
may impose a newer Windows version. The API is invoked in ordinary user mode.

[Microsoft SDL cryptographic recommendations](https://learn.microsoft.com/en-us/security/engineering/cryptographic-recommendations)
recommends BCryptGenRandom with the system-preferred RNG flag for CNG randomness.
Neither source makes a random nonce an OS boot ID or a lifetime capability.
