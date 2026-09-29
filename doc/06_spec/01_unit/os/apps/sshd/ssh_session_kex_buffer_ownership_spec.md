# SSH session KEX bounded buffer and runtime ownership

> Unit and source-contract manual for the pure bounded SSH KEX encoder and its
> canonical freestanding crypto owner.

| Tests | Passed | Failed | Evidence class |
|------:|-------:|-------:|----------------|
| 11 | 11 | 0 | Unit + source contract |

## Purpose and audience

This manual is for SSH, crypto, and SimpleOS maintainers reviewing the
key-exchange boundary. It demonstrates that SSH wire assembly uses the pure,
bounded `SshKexByteBuffer`, that capacity errors discard partial output, and
that four unavoidable freestanding crypto ABI hooks remain behind the
canonical library owner.

## Scope and preconditions

Run the executable spec from the repository root with an admitted pure-Simple
test runner. The scenarios cover deterministic buffer behavior, published RFC
7748 X25519 vectors, and source ownership contracts.

## Primary operator workflow

1. Review the encoder and boundary scenarios before changing SSH packet
   assembly.
2. Review both RFC 7748 anchors before changing the pure X25519 path.
3. Review the ownership scenarios before moving runtime crypto or time calls.
4. Treat a mismatch, partial result, raw app-level runtime hook, or missing
   full-length comparison barrier as a regression.

## Requirements and traceability

| Requirement | Behavior | Scenarios |
|-------------|----------|-----------|
| REQ-SSH-KEX-BUFFER-001 | Bounded pure encoding is byte-correct and discards partial output after failure. | 5 |
| REQ-SSH-KEX-CRYPTO-001 | Pure X25519 matches the RFC 7748 public-key and shared-secret vectors. | 2 |
| REQ-SSH-KEX-OWNER-001 | Session code uses canonical owners and a full-length comparison barrier. | 4 |

Lifecycle context:

- `doc/01_research/lib/crypto/security_crypto_protocol_catalog_2026-06-15.md`
- `doc/03_plan/sys_test/rv64_ssh_live_login_in_qemu.md`
- `doc/04_architecture/lib/ssh_algorithm_catalog.md`
- `doc/05_design/rv64_sv39_pid1_network_ssh_wm_boot.md`

## Scenario narratives

### Bounded byte buffer

1. **Encode one SSH uint32 in network byte order.** Expected outcome: the four
   bytes are `01 02 03 04`.
2. **Build the Ed25519 signature blob with both encoders.** Expected outcome:
   byte-for-byte parity and an 83-byte SSH blob.
3. **Submit an invalid Ed25519 signature length.** Expected outcome: rejection
   naming the 64-byte contract, with no partial output.
4. **Cross exact capacity by one byte.** Expected outcome: fail-closed capacity
   error and no partial output.
5. **Request a limit above the protocol maximum.** Expected outcome:
   construction finishes as an error.

### Pure X25519 anchors

6. **Derive the RFC 7748 public key.** Expected outcome: exact equality with
   Alice's published 32-byte public key.
7. **Compute the RFC 7748 shared secret.** Expected outcome: exact equality
   with the published 32-byte shared secret.

### Runtime ownership

8. **Inspect session and buffer modules for raw runtime hooks.** Expected
   outcome: neither module declares `extern fn rt_` or uses `rt_push_byte`.
9. **Inspect session imports and calls.** Expected outcome: crypto calls route
   through `std.nogc_sync_mut.crypto.ssh_kex_runtime`, while sleeping routes
   through `std.nogc_sync_mut.io.time_ops`.
10. **Inspect the canonical crypto owner.** Expected outcome: exactly the four
    X25519, SHA-256, and exchange-hash ABI declarations are owned there, with
    no byte-push hook.
11. **Inspect the parity comparison.** Expected outcome: full-length XOR/OR
    accumulation reaches `black_box`; the obsolete helper is absent.

## Evidence and provenance

The executable spec retains one value-derived text capture per scenario and
binds every scenario to a requirement. RFC 7748 vectors are independent
cryptographic oracles. Source inspection is supporting ownership evidence, not
endpoint behavior evidence.

- Executable source:
  `test/01_unit/os/apps/sshd/ssh_session_kex_buffer_ownership_spec.spl`
- Source SHA-256:
  `1dac513a316c3e29353fe0dfe9cf1390be7b3950029897c325a1138341b766c6`
- Current recorded unit result: 11 passed, 0 failed.

<details>
<summary>Executable SSpec</summary>

The complete executable source is the canonical file linked above. It contains
the 11 scenario bodies, literal `step("...")` calls, assertions, requirement
bindings, and captures mirrored by this manual.

</details>

## Verification and troubleshooting

Expected verification is 11 passed and 0 failed. For encoder failures, inspect
the captured length or error before the byte comparison. For vector failures,
compare the pure X25519 output with RFC 7748. For ownership failures, restore
the typed crypto/time imports and keep raw ABI declarations in the canonical
library owner.

## Documentization scorecard and findings

The requested maintenance scan was not rerun during this documentation-only
handoff because no admitted pure-Simple `sspec-maintain` executable was
available in the lane. No scan score is claimed. The source and mirror now
contain the professional narrative, visible workflow, requirement bindings,
typed evidence descriptions, lifecycle links, recovery guidance, and explicit
limitations needed for a later canonical scan.

## Compatibility and limitations

This is unit and source-contract evidence. It does not claim an admitted Stage
4 executable, a complete live SSH handshake, QEMU boot, or OpenSSH
interoperability. Those remain separate integration and release gates; no
Stage 4 evidence is created or inferred here.

## Generation history

This mirror was authored from source SHA-256
`1dac513a316c3e29353fe0dfe9cf1390be7b3950029897c325a1138341b766c6` after
the canonical documentization command was unavailable in this lane. Regenerate
through the admitted pure-Simple SPipe/documentization owner when that runtime
is restored.
