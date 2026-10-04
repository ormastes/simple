# Mach-O static-link fixtures

Compile these assembly inputs with LLVM clang (no Apple SDK or runtime needed):

```text
clang --target=x86_64-apple-macos11 -c start_x64.s -o start_x64.o
clang --target=x86_64-apple-macos11 -c provider_x64.s -o provider_x64.o
clang --target=arm64-apple-macos11 -c start_a64.s -o start_a64.o
clang --target=arm64-apple-macos11 -c start_a64_add.s -o start_a64_add.o
clang --target=arm64-apple-macos11 -c provider_a64.s -o provider_a64.o
llvm-ar --format=darwin rcs provider_x64.a provider_x64.o
llvm-ar --format=gnu rcs provider_a64.a provider_a64.o
llvm-readobj --file-headers --sections --symbols --relocations start_x64.o start_a64.o
```

Compile `mid_x64.s`, `leaf_x64.s`, `weak_x64.s`, `common_x64.s`, and
`common_large_x64.s` with the same x86_64 command. Build the transitive archive
with `llvm-ar --format=darwin rcs chain_x64.a leaf_x64.o mid_x64.o` (leaf first,
so the entry's initially unresolved `_helper` cannot accidentally select it).

These are real MH_OBJECT inputs. The linker result must be MH_EXECUTE, with
mapped segments and LC_UNIXTHREAD; object emission is not executable evidence.
The x86_64 call patch is +3 after 4-byte input-section alignment. The ARM64
BL patch is +16 bytes. ARM64 ADRP targets the data segment, and LDR encodes its
scaled page offset. Neither fixture requires dyld or TLS. Native Darwin loader
admission, including signing policy, remains separate from image construction.

Wire authorities: [Apple loader.h](https://github.com/apple-oss-distributions/xnu/blob/main/EXTERNAL_HEADERS/mach-o/loader.h)
defines executable/segment/thread commands; [LLVM MachO.h](https://llvm.org/doxygen/BinaryFormat_2MachO_8h_source.html)
defines relocation and thread-state records. Hosted ARM64 signing is a separate
gate, illustrated by [LLD's ad-hoc signing tests](https://github.com/llvm/llvm-project/blob/main/lld/test/MachO/adhoc-codesign.s).

## Actual dylib dependency fixtures

Generated using the installed LLVM `ld64.lld` (Windows LLVM distribution), without
an Apple SDK. These are dependency-reader fixtures, not Darwin execution evidence.

```text
ld64.lld -dylib -arch x86_64 -platform_version macos 11.0 11.0 -install_name @rpath/libitem4.dylib -current_version 2.3.4 -compatibility_version 1.2 -o provider_x64.dylib provider_x64.o
ld64.lld -dylib -arch arm64 -platform_version macos 11.0 11.0 -install_name @rpath/libitem4.dylib -current_version 2.3.4 -compatibility_version 1.2 -o provider_a64.dylib provider_a64.o
ld64.lld -dylib -arch x86_64 -platform_version macos 11.0 11.0 -install_name @rpath/libitem4_reexport.dylib -reexport_library provider_x64.dylib -o reexport_x64.dylib
llvm-objdump --macho --exports-trie --dylibs-used provider_x64.dylib provider_a64.dylib reexport_x64.dylib
```

LLVM inspection reports x64 `_helper=0x2d8`, `_value=0x1000`; arm64
`_helper=0x2e8`, `_value=0x4000`. The reexport fixture has one LC_REEXPORT_DYLIB
dependency and zero direct trie exports. Version values are independently checked
as packed 2.3.4 (`0x20304`) and 1.2.0 (`0x10200`).

## Hosted input fixtures

Compile `hosted_start_x64.s` / `hosted_tlv_x64.s` with the x86_64 clang command,
and `hosted_start_a64.s` / `hosted_tlv_a64.s` with the arm64 command. These inputs
preserve the main-call ABI stack alignment/return address. Inspect with
`llvm-readobj --relocations`. Compile `hosted_tls_provider.s` for both targets,
then produce `hosted_tls_x64.dylib` and `hosted_tls_a64.dylib` with:

```text
ld64.lld -dylib -arch x86_64 -platform_version macos 11.0 11.0 -install_name @rpath/libitem4_tls.dylib -undefined dynamic_lookup -o hosted_tls_x64.dylib hosted_tls_provider_x64.o
ld64.lld -dylib -arch arm64 -platform_version macos 11.0 11.0 -install_name @rpath/libitem4_tls.dylib -undefined dynamic_lookup -o hosted_tls_a64.dylib hosted_tls_provider_a64.o
llvm-objdump --macho --exports-trie hosted_tls_x64.dylib hosted_tls_a64.dylib
```

LLVM identifies `_tls` as a per-thread export at x64 `0x1000` / arm64 `0x4000`.
`-undefined dynamic_lookup` is explicit fixture linkage for `__tlv_bootstrap`;
it is not an admitted SDK or runtime substitute. Executable reference generation
with ld64 was attempted once and rejected missing `dyld_stub_binder`; no such
reference executable or successful execution is claimed.

Independent page-hash oracle: .NET `SHA256.HashData` over 4096 zero bytes yields
`ad7facb2586fc6e966c004d7d1d16b024f5805ff7cb47c7a85dabd8b48892ca7`.

## Duplicate-definition policy fixtures (2026-10-04)

Constructed under WSL Ubuntu using `Ubuntu clang version 21.1.8 (6ubuntu1)`
and `Ubuntu LLVM version 21.1.8` (`llvm-ar`). Commands run from this fixture
directory, so `.include` names resolve to the checked-in assembly sources:

```sh
clang --target=x86_64-apple-macos11 -c duplicates_entry_x64.s duplicates_a_x64.s duplicates_b_x64.s
clang --target=arm64-apple-macos11 -c duplicates_entry_a64.s duplicates_a_a64.s duplicates_b_a64.s
clang --target=x86_64-apple-macos11 -c duplicates_archive_entry_x64.s duplicates_archive_member_x64.s duplicates_leaf_x64.s
llvm-ar rcs duplicates_chain_x64.a duplicates_leaf_x64.o duplicates_archive_member_x64.o
llvm-ar rcs duplicates_unused_x64.a duplicates_b_x64.o
clang --target=x86_64-apple-macos11 -c duplicates_weak_a_x64.s duplicates_weak_b_x64.s duplicates_common_x64.s duplicates_common_large_x64.s
```

Archive member order is intentionally leaf before demanded member: `_trigger`
selects the later member, whose `_leaf` reference requires another closure pass.
The demanded member also introduces the competing22 definitions. The unused
archive contains only B, with no new demand. A/B code and data distinguish11/22;
weak variants retain the same payload with weak-definition symbol flags. Common
declarations are size8/align8 and size32/align32. These are external assembly
construction results only, not Simple SSpec or Darwin execution evidence.

## TextAPI fixtures (2026-10-04)

Tool: WSL Ubuntu `llvm-readtapi`, LLVM21.1.8. All binary sources above are
repository-authored, not copied Apple SDK material. Run in this directory:

```sh
llvm-readtapi -stubify --filetype=tbd-v4 provider_x64.dylib -o tbd_provider_x64_v4.tbd
llvm-readtapi -stubify --filetype=tbd-v5 provider_x64.dylib -o tbd_provider_x64_v5.tbd
llvm-readtapi -stubify --filetype=tbd-v5 provider_a64.dylib -o tbd_provider_a64_v5.tbd
llvm-readtapi -merge --filetype=tbd-v4 tbd_provider_x64_v4.tbd tbd_provider_a64_v5.tbd -o tbd_provider_multi_v4.tbd
llvm-readtapi -merge --filetype=tbd-v5 tbd_provider_x64_v4.tbd tbd_provider_a64_v5.tbd -o tbd_provider_multi_v5.tbd
llvm-readtapi -compare tbd_provider_multi_v4.tbd tbd_provider_multi_v5.tbd
llvm-readtapi -stubify --filetype=tbd-v4 hosted_tls_x64.dylib -o tbd_tls_x64_v4.tbd
llvm-readtapi -stubify --filetype=tbd-v5 hosted_tls_a64.dylib -o tbd_tls_a64_v5.tbd
llvm-readtapi -stubify --filetype=tbd-v5 tbd_metadata_v4.tbd -o tbd_metadata_v5.tbd
llvm-readtapi -compare tbd_metadata_v4.tbd tbd_metadata_v5.tbd
llvm-readtapi -extract --arch=x86_64 --filetype=tbd-v4 tbd_metadata_v5.tbd -o tbd_metadata_x64_oracle_v4.tbd
```

The metadata v4 file is authored YAML with target-only exports, ObjC categories,
weak/TLV names, restrictions and an inline reexported child. Conversion,
comparison and extraction succeeded. V4 cannot preserve deployment metadata;
the merged V5 fixture therefore omits x64 min_deployment while retaining arm64
11.0 from its binary-derived V5 source. No SDK value is invented.

LLVM rejects duplicate YAML mapping keys and the truncated fixtures. LLVM21
accepts repeated identical JSON version keys; our planned duplicate-key refusal
is intentionally stricter, not an LLVM-equivalence claim. The v5 duplicate-key
file repeats version5 so an unrelated wrong-version error cannot mask that test.
These are external TextAPI construction/validation observations, not Simple
test execution, client-access approval, transitive linker or Darwin SDK proof.
