# RISC-V UART baud policy native performance gap

Status: resolved in the isolated optimization candidate; authoritative merge
and pure-Simple release verification remain pending.

The pure-Simple RISC-V 16550 baud-policy candidate has exact result parity
with its C oracle, but the Rust-seed Cranelift artifact is not yet comparable
in performance. On the same host and the same 50,000,000-case mixed workload,
both implementations produced checksum `513661653`:

- C (`clang-20 -O2`): 0.18 s, 1,536 KiB maximum RSS.
- Simple (`--native --backend=cranelift --opt-level=aggressive`): 3.95 s,
  2,345,472 KiB maximum RSS.
- Observed ratio: 21.94x wall time and about 1,527x maximum RSS.

Acceptance target: Simple/C wall time must be at most 3.0x on the shared
50,000,000-case workload, with matching checksum and without material RSS
regression. Profile the seed-native allocation/runtime startup and the hot
`uart_baud_plan` call before changing policy semantics. Re-run the comparable
pair once after the profile-backed fix.

Frozen raw evidence is in `build/mini_builds/hal_uart_policy_20260820/` of the
integration lane. This candidate was not verified with the pure-Simple
self-host because the focused native build exceeded the bounded 60-second
diagnostic window; do not treat Rust-seed evidence as release acceptance.

Coverage caveat: the Rust seed measured 9/9 policy decisions at 100%, but its
coverage serializer attributes imported policy locations to the probe source.
Preserve the raw SDN and fix/verify source attribution before using it as a
whole-module release claim.

## Isolated resolution evidence

The generated native loop allocated one boxed `UartBaudPlan` per case and
Cranelift emitted an integer division for `i % 115199` that clang strength-
reduced. The policy now has a scalar word core for decision-only scans while
the existing plan/MMIO API constructs the same public values. The benchmark
maintains the identical remainder sequence explicitly.

On the same retained 50,000,000-case model, the optimized Simple artifact
produced checksum `513661653` in 0.46 s / 3,584 KiB. Against the retained
0.18 s C row, the ratio is 2.56x and passes the <=3.0x gate. Shared-vector
parity remains 8/8 and decision coverage is 13/13 (100%). These are isolated
Rust-seed-native optimization results, not a pure-Simple release claim.
