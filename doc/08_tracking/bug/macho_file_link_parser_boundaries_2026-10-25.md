# Mach-O file-link parser boundaries — 2026-10-25

## Failure and repair

The canonical `link_freestanding_to_native_v1` file adapter could publish ELF
images but failed for real Mach-O object/archive inputs. Three parser boundary
errors prevented the internal Mach-O engine from resolving and relocating them:

1. `command.? == false` compared an optional command with a boolean. An absent
   `LC_UUID` or `LC_SYMTAB` reached a forced unwrap. Test the optional against
   `nil`, matching `macho_find_load_command`'s contract.
2. Section and symbol names were decoded one byte at a time with
   `text.from_char_code(u8)`. This treats UTF-8 bytes as separate code points;
   the retained diagnostic seed additionally turns its unsigned byte argument
   into NUL (the existing COFF parser documents the same producer limitation).
   Decode a bounded NUL-terminated byte slice through the canonical
   `std.common.text_bytes.bytes_to_text` owner instead.
3. Unsigned `BinaryReader` values remained unsigned carriers in the parser's
   declared `i64` record fields. In the diagnostic producer, adding the u32
   relocation offset to Mach-O's `0x100000000` VM base narrowed the result:
   address `4294983680` plus offset `1` produced `16385`. Convert wire fields
   explicitly to the signed model before linker address arithmetic. The shared
   relocation oracle itself computed the correct displacement `3` when supplied
   full-width inputs; no relocation formula or struct ABI changed.

The new parser spec covers absent commands, present UUID bytes (including zero
and high bytes), real symbol/section names, UTF-8 symbol identity, and arithmetic
above four GiB. Existing core tests cover actual relocations, archive closure,
weak/common symbols, malformed inputs, unsupported relocations, and size bounds.

## Scoped verification

Source base: `73c4aef632ab306366b558468f9d7e65e4780030` on `release/1.0.0`.
Isolated workspace: `/Users/ormastes/wt/simple-linker-files-20261025`.
Evidence directory: `build/verify/simple-linker-files-20261025/`.

The existing bootstrap seed was used only for explicitly authorized interpreter
diagnostics, with `SIMPLE_LIB=<workspace>/src` and:

```sh
"$EXISTING_SEED" test "$SPEC" --mode=interpreter --no-session-daemon \
  --sequential --no-db --no-cache --assert-ran
```

Producer SHA-256:
`ddd5aa4b9c47433ac814983d7499002a115e9f0e28f4623bfe26dba7e6b0a714`.
Its retained generation is
`aa58a24ebe00248b428d4507e5cb0c58ec497c28ec8b2a3ed71ec65d697f756c-ecd1ed1cbf3f68a7abc6c2f852358542fae0b6e2e66c88e5abfcd5ea22cb3d2b`.
The frozen pure-Simple Phase2 binary rejects the public `run` command; its
failure is preserved in `baseline-elf-driver.log`, not counted as linker proof.

| Spec | Baseline | Final |
| --- | --- | --- |
| `macho_optional_commands_spec.spl` | New regression | 5 passed, 0 failed |
| `item4_freestanding_adapter_spec.spl` | 5 passed, 1 failed | 6 passed, 0 failed |
| `item4_linker_macho_spec.spl` | 2 passed, 14 failed | 16 passed, 0 failed |

Final logs are `fixed3-{optional,file-adapter,macho-core}.log`; exact argv is
stored alongside each. Earlier baseline and intermediate failure logs remain.
Three fix/verification cycles were used; passing checks were not repeated after
convergence. A separate ARM64 file-publication probe added two previously
uncovered file configurations and retained these outputs:

| Actual internal-linker output | Bytes | SHA-256 |
| --- | ---: | --- |
| `linked-arm64.macho` | 32776 | `5642ec7bd4f561b3ec8fec95c6d6c90c29576cd8cdb11b299f01c756e0e105fa` |
| `linked-arm64.elf` | 1464 | `5e49f217919fb1a675ab979589a90bbaa8589ac7d5586da90965a4afaf69bf78` |

The Mach-O probe links `start_a64.o` plus `provider_a64.a`; the ELF probe links
`start_a64.o` plus transitive `libchain_a64.a`. They invoke the canonical Simple
file adapter and report `internal:macho` / `internal:elf`. No system linker
produced either image. Independent byte inspection verified Mach-O ARM64
`MH_EXECUTE`, `LC_UNIXTHREAD` PC `0x100004000`, exact BL/ADRP/LDR instructions,
and ELF AArch64 `ET_EXEC` with entry inside executable `PT_LOAD`. Apple's
`otool -hv` independently recognizes the Mach-O executable.

This is actual file-link/image evidence under an interpreter, not qualification
of a rebuilt pure-Simple native producer. Static Mach-O output does not establish
dyld, signing, or Darwin loader admission. ELF outputs were not executed on this
macOS host. Hosted linking, PE/COFF, and other unsupported configurations were
not qualified. No compiler, runtime, Phase2, or full-bootstrap rebuild was run;
the separate live Phase3 source trees were left unchanged. Broad compiler/MCP
checks that would require unavailable normal tooling remain outside this
restricted diagnostic verification.
