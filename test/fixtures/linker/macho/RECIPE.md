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
llvm-readtapi -stubify --filetype=tbd-v4 provider_x64.dylib -o tbd_provider_x64_v4_interface.tbd
llvm-readtapi -stubify --filetype=tbd-v5 provider_x64.dylib -o tbd_provider_x64_v5_interface.tbd
llvm-readtapi -stubify --filetype=tbd-v5 provider_a64.dylib -o tbd_provider_a64_v5_interface.tbd
llvm-readtapi -merge --filetype=tbd-v4 tbd_provider_x64_v4_interface.tbd tbd_provider_a64_v5_interface.tbd -o tbd_provider_multi_v4_interface.tbd
llvm-readtapi -merge --filetype=tbd-v5 tbd_provider_x64_v4_interface.tbd tbd_provider_a64_v5_interface.tbd -o tbd_provider_multi_v5_interface.tbd
llvm-readtapi -compare tbd_provider_multi_v4_interface.tbd tbd_provider_multi_v5_interface.tbd
llvm-readtapi -stubify --filetype=tbd-v4 hosted_tls_x64.dylib -o tbd_tls_x64_v4_interface.tbd
llvm-readtapi -stubify --filetype=tbd-v5 hosted_tls_a64.dylib -o tbd_tls_a64_v5_interface.tbd
llvm-readtapi -stubify --filetype=tbd-v5 tbd_metadata_v4_interface.tbd -o tbd_metadata_v5_interface.tbd
llvm-readtapi -compare tbd_metadata_v4_interface.tbd tbd_metadata_v5_interface.tbd
llvm-readtapi -extract --arch=x86_64 --filetype=tbd-v4 tbd_metadata_v5_interface.tbd -o tbd_metadata_x64_oracle_v4_interface.tbd
llvm-readtapi -stubify --filetype=tbd-v5 tbd_leaf_metadata_v4_interface.tbd -o tbd_leaf_metadata_v5_interface.tbd
llvm-readtapi -compare tbd_leaf_metadata_v4_interface.tbd tbd_leaf_metadata_v5_interface.tbd
llvm-readtapi -extract --arch=x86_64 --filetype=tbd-v5 tbd_inline_unmatched_v5_interface.tbd -o /tmp/item4-inline-unmatched-oracle-20261004.tbd
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

The `tbd_bad_unselected_*`, `tbd_duplicate_unselected_*`,
`tbd_escaped_duplicate_key_v5`, `tbd_wrong_version_*`,
`tbd_version_overflow_*`, `tbd_arm64e_only_v4`, `tbd_catalyst_only_v5` and
`tbd_ld_directive_*` fixtures are hand-authored schema/selection regressions.
They were not revalidated through LLVM: invalid all-target metadata and decoded
duplicate-key refusal belong to our frozen strict reader contract, while `$ld$`
policy is deliberately unsupported by leaf lowering. They do not extend the
external conversion/comparison PASS observations recorded above.

Final targeted YAML fixture `tbd_quoted_flow_v4_interface.tbd` was accepted once by:
`llvm-readtapi -extract --arch=x86_64 --filetype=tbd-v4 tbd_quoted_flow_v4_interface.tbd -o /tmp/item4-quoted-flow-oracle-20261004.tbd`.
Its longest decoded quoted name is32 bytes. The two hand-authored
`tbd_bad_mapping_separator_v4`/`tbd_bad_target_separator_v4` cases omit YAML
mapping separator whitespace and are strict-reader rejection inputs; no prior
successful external check was repeated.

## Stage 3 provider closure fixtures (2026-10-04)

All commands below ran from `test/fixtures/linker/macho` in WSL Ubuntu with
LLVM 21.1.8 (Ubuntu clang 21.1.8 6ubuntu1). This is external construction and
inspection evidence only; all Simple closure tests remain UNRUN.

The root, leaf, whole-library cycle, restricted-client and alias-sibling v4
interfaces are authored inputs. Their v5 counterparts were converted with:

```
llvm-readtapi -stubify --filetype=tbd-v5 closure_root_v4_interface.tbd -o closure_root_v5_interface.tbd
llvm-readtapi -stubify --filetype=tbd-v5 closure_leaf_v4_interface.tbd -o closure_leaf_v5_interface.tbd
llvm-readtapi -stubify --filetype=tbd-v5 closure_cycle_v4_interface.tbd -o closure_cycle_v5_interface.tbd
llvm-readtapi -stubify --filetype=tbd-v5 closure_restricted_v4_interface.tbd -o closure_restricted_v5_interface.tbd
llvm-readtapi -stubify --filetype=tbd-v5 closure_alias_sibling_v4_interface.tbd -o closure_alias_sibling_v5_interface.tbd
llvm-readtapi -compare closure_root_v4_interface.tbd closure_root_v5_interface.tbd
llvm-readtapi -compare closure_cycle_v4_interface.tbd closure_cycle_v5_interface.tbd
```

Each command succeeded once. No LLVM client-access authorization is inferred.
The alias entry assembly differs from the earlier hosted entry only by calling
`_alias` instead of `_helper`. Exact construction:

```
clang --target=x86_64-apple-macos11 -c closure_alias_entry_x64.s
clang --target=arm64-apple-macos11 -c closure_alias_entry_a64.s
ld64.lld -dylib -arch x86_64 -platform_version macos 11 11 -install_name /usr/lib/libitem4_alias_leaf.dylib -o closure_alias_leaf_x64.dylib provider_x64.o
ld64.lld -dylib -arch arm64 -platform_version macos 11 11 -install_name /usr/lib/libitem4_alias_leaf.dylib -o closure_alias_leaf_a64.dylib provider_a64.o
ld64.lld -dylib -arch x86_64 -platform_version macos 11 11 -install_name /usr/lib/libitem4_alias.dylib -reexport_library closure_alias_leaf_x64.dylib -o closure_alias_x64.dylib
ld64.lld -dylib -arch arm64 -platform_version macos 11 11 -install_name /usr/lib/libitem4_alias.dylib -reexport_library closure_alias_leaf_a64.dylib -o closure_alias_a64.dylib
```

LLD's attempted `-alias _helper _alias` with a reexport provider failed with
`TODO: support aliasing to symbols of kind 3`. Accordingly the two real binary
roots above were explicitly mutated, rather than described as LLD-generated
aliases. Append the following export trie byte sequence at original EOF:
`00 01 5f 61 6c 69 61 73 00 0a 0a 08 01 5f 68 65 6c 70 65 72 00 00`.
Set LC_DYLD_INFO_ONLY export offset/size to that appended span, extend __LINKEDIT
file size to EOF and round its VM size up to16384. It encodes `_alias`, flags8,
reexport dependency ordinal1, import `_helper`. Existing signatures are not
recomputed: no signature validity or Darwin loading claim is made.

`closure_alias_cycle_x64.dylib` derives from this checked-base x64 root. Its
LC_REEXPORT_DYLIB name is replaced within the existing command by
`/usr/lib/a.dylib` and zero padding. The alias terminal size changes10 to9;
import bytes become `_alias` plus NUL and the next child-count byte remains0.
The v4/v5 sibling fixture's A reexports this binary B before inline C; C defines
`_alias`. This is an intentional mixed alias-cycle regression.

Independent observations, each executed once:

```
llvm-objdump --macho --exports-trie closure_alias_x64.dylib closure_alias_a64.dylib
llvm-objdump --macho --exports-trie closure_alias_cycle_x64.dylib
```

The first prints `[re-export] _alias (_helper from libitem4_alias_leaf)` for
both CPUs; the second prints `[re-export] _alias (_alias from a)`. These are
binary export-trie observations, not application execution or a fake provider
VM-address construction. No new archive ordering is involved in this lane.

The hand-authored closure_future_leaf_v5_interface.tbd requires macOS 12.0 for
a reachable x64 leaf under a macOS 11 request. Its specific minimum-OS rejection
and destination preservation are authored acceptance, not an external LLVM or
Simple execution claim.

## Owner-rpath provider fixture construction (2026-10-04)

From this fixture directory, Ubuntu LLVM21.1.8 built actual x64/ARM64 providers:

```
ld64.lld -dylib -arch x86_64 -platform_version macos 11 11 -install_name @rpath/libitem4_rpath_leaf.dylib -o rpath_leaf_x64.dylib provider_x64.o
ld64.lld -dylib -arch arm64 -platform_version macos 11 11 -install_name @rpath/libitem4_rpath_leaf.dylib -o rpath_leaf_a64.dylib provider_a64.o
ld64.lld -dylib -arch x86_64 -platform_version macos 11 11 -install_name /usr/lib/libitem4_rpath_root.dylib -rpath @loader_path/first -rpath @loader_path/second -reexport_library rpath_leaf_x64.dylib -o rpath_root_x64.dylib
ld64.lld -dylib -arch arm64 -platform_version macos 11 11 -install_name /usr/lib/libitem4_rpath_root.dylib -rpath @loader_path/first -rpath @loader_path/second -reexport_library rpath_leaf_a64.dylib -o rpath_root_a64.dylib
llvm-objdump --macho --rpaths rpath_root_x64.dylib rpath_root_a64.dylib
llvm-readtapi -extract --arch=x86_64 --filetype=tbd-v5 rpath_root_v5_interface.tbd -o /tmp/item4-rpath-x64-oracle-20261004.tbd
llvm-readtapi -extract --arch=arm64 --filetype=tbd-v5 rpath_root_v5_interface.tbd -o /tmp/item4-rpath-a64-oracle-20261004.tbd
```

Commands succeeded once. Objdump reports `@loader_path/first`, then
`@loader_path/second` for each binary root. The authored v5 interface scopes
`@loader_path/x64` or `@loader_path/a64` before the common second directory.
Readtapi accepted both selected targets. These observations establish fixture
metadata only, not inherited dyld search behavior, Simple execution, or Darwin
loading/signing qualification. The underlying provider object assembly and
commands are documented earlier in this recipe.

Additional owner-context fixtures use the same LLVM21.1.8 fixture-directory cwd:

```
ld64.lld -dylib -arch x86_64 -platform_version macos 11 11 -install_name /usr/lib/libitem4_rpath_peer.dylib -rpath @loader_path/first -reexport_library rpath_leaf_x64.dylib -o rpath_peer_x64.dylib
ld64.lld -dylib -arch x86_64 -platform_version macos 11 11 -install_name /usr/lib/libitem4_rpath_middle.dylib -reexport_library rpath_leaf_x64.dylib -o rpath_middle_x64.dylib
llvm-objdump --macho --rpaths rpath_peer_x64.dylib
llvm-objdump --macho --rpaths rpath_middle_x64.dylib
llvm-readtapi -extract --arch=x86_64 --filetype=tbd-v5 rpath_inline_v5_interface.tbd -o /tmp/item4-rpath-inline-oracle-20261004.tbd
llvm-readtapi -extract --arch=x86_64 --filetype=tbd-v5 rpath_inline_cycle_v5_interface.tbd -o /tmp/item4-rpath-inline-cycle-oracle-20261004.tbd
llvm-readtapi -extract --arch=x86_64 --filetype=tbd-v5 rpath_ancestor_v5_interface.tbd -o /tmp/item4-rpath-ancestor-oracle-20261004.tbd
```

Each listed command succeeded once. Peer has `@loader_path/first`; Middle has
no LC_RPATH. The three authored v5 documents preserve explicit inline provider
priority, a bounded inline cycle, and an ancestor-owned path that must not be
borrowed by an external Middle. An attempted binary ancestor construction via
`-reexport_library rpath_middle_x64.dylib` without additional dependency search
failed to locate Middle's @rpath leaf; it produced no retained ancestor fixture.
The committed ancestor is explicitly authored TBD metadata, not a claimed
LLD-generated binary. No Simple or Darwin execution was performed.

## Legacy reexport selector fixtures (2026-10-04)

These are real Ubuntu LLVM21.1.8 binaries plus explicitly documented command
mutations. Commands ran from this fixture directory. For each pair
`SUFFIX=x64, ARCH=x86_64` and `SUFFIX=a64, ARCH=arm64`:

```
ld64.lld -dylib -arch ARCH -platform_version macos 11 11 -install_name /usr/lib/liblegacy.1.dylib -o legacy_leaf_SUFFIX.dylib provider_SUFFIX.o
ld64.lld -dylib -arch ARCH -platform_version macos 11 11 -install_name /usr/lib/liblegacy_root.dylib -needed_library legacy_leaf_SUFFIX.dylib -o legacy_ordinary_SUFFIX.dylib
ld64.lld -dylib -arch ARCH -platform_version macos 11 11 -install_name /System/Library/Frameworks/Leaf.framework/Leaf -o legacy_framework_leaf_SUFFIX.dylib provider_SUFFIX.o
ld64.lld -dylib -arch ARCH -platform_version macos 11 11 -install_name /usr/lib/liblegacy_root.dylib -needed_library legacy_framework_leaf_SUFFIX.dylib -o legacy_framework_ordinary_SUFFIX.dylib
```

`ARCH` and `SUFFIX` above are explicit substitution labels, not literal shell
arguments. The paired provider assembly/object provenance appears earlier.
The roots contain real LC_LOAD_DYLIB commands and header flags0x100085.
A24-byte LC_UUID command is replaced in-place by LC_SUB_LIBRARY0x15 with
string `liblegacy`, or LC_SUB_UMBRELLA0x13 with `Leaf`. Set the command's
relative string offset to12, zero the remaining payload and copy the ASCII name
plus NUL. `legacy_{library,umbrella}_suppressed_SUFFIX.dylib` preserves the
original header flag. `legacy_{library,umbrella}_SUFFIX.dylib` clears only
MH_NO_REEXPORTED_DYLIBS0x100000. Original dependency commands/ordinals stay intact.

Both CPUs' active variants were independently decoded once by:

```
llvm-objdump --macho --private-headers legacy_library_x64.dylib legacy_library_a64.dylib legacy_umbrella_x64.dylib legacy_umbrella_a64.dylib
```

Observed command payloads were `sub_library liblegacy (offset 12)` and
`sub_umbrella Leaf (offset 12)`, each cmdsize24. These are documented mutations,
not a claim LLD emitted those legacy commands itself.

`legacy_modern_hidden_SUFFIX.dylib` derives from the ordinary library root by
clearing only0x100000. `legacy_classic_root_SUFFIX.dylib` additionally replaces
its empty48-byte LC_DYLD_INFO_ONLY command with a40-byte LC_NOTE named
`item4classic`, offset0/size0. Move the remaining load commands left8 bytes,
decrease sizeofcmds by8, and zero the vacated8 header bytes; ncmds and all
section/file addresses remain unchanged. This removes the modern export source
while preserving the existing validated symbol-table fallback. An initial
48-byte LC_NOTE attempt was rejected by llvm-objdump for incorrect cmdsize;
only the corrected40-byte form is committed.

`legacy_child_OldRoot_SUFFIX.dylib` and `legacy_child_Different_SUFFIX.dylib`
derive from the corresponding real leaf by replacing UUID24 with
LC_SUB_FRAMEWORK0x12, offset12, and the stated NUL-terminated umbrella name.
The test's macOS99 child is a separate guarded runtime mutation of the actual
LC_BUILD_VERSION minimum/SDK words; the committed child remains macOS11.

```
llvm-objdump --macho --private-headers legacy_classic_root_x64.dylib legacy_classic_root_a64.dylib legacy_child_OldRoot_x64.dylib legacy_child_OldRoot_a64.dylib
```

The corrected command observation succeeded, reporting LC_NOTE size40 and
`umbrella OldRoot (offset 12)`. No successful observation was rerun.

The classic root with its own exports starts with this additional real link:

```
ld64.lld -dylib -arch x86_64 -platform_version macos 11 11 -install_name /usr/lib/liblegacy_root.dylib -needed_library legacy_leaf_x64.dylib -o legacy_classic_own_x64.dylib provider_x64.o
```

Apply the same suppression-bit clear and corrected LC_NOTE conversion above.
Independent `llvm-nm --defined-only --extern-only legacy_classic_own_x64.dylib`
then reported `_helper` at0x318 and `_value` at0x1000. Tests still call the actual
validating binary reader before relying on the fallback exports.

Signatures are not regenerated after mutations. These fixtures establish
reader/graph byte contracts only: no code-signing validity, Darwin loadability,
Simple execution, or full SDK completion is claimed.

Final all-match and modes fixtures derive from the already validated binaries:
`legacy_all_matches_x64.dylib` copies the LC_LOAD_DYLIB command in
`legacy_library_x64.dylib` into verified all-zero header padding before byte4096,
changes the copied install name to `/usr/lib/liblegacy.2.dylib`, and increments
ncmds/sizeofcmds by1/the copied command size. Existing offsets do not move.
`legacy_empty_first_x64.dylib` copies the ordinary no-export root and changes
only LC_ID_DYLIB to `/usr/lib/liblegacy.1.dylib`; its original header suppression
and modern format keep its own ordinary dependency hidden.
`legacy_second_x64.dylib` changes only the real leaf's LC_ID_DYLIB to
`/usr/lib/liblegacy.2.dylib`. Command-relative string capacity and zero padding
were checked before each mutation.

```
llvm-objdump --macho --dylibs-used legacy_all_matches_x64.dylib
llvm-nm --defined-only --extern-only legacy_empty_first_x64.dylib legacy_second_x64.dylib
```

The first independently reports root then .1 then .2 install identities.
The first provider has no symbols; the second exports `_helper`0x2e0 and
`_value`0x1000. Thus the native image test cannot succeed with only the first
matching edge.

The separate modes lane uses a modern root with its own exports:

```
ld64.lld -dylib -arch x86_64 -platform_version macos 11 11 -install_name /usr/lib/liblegacy_root.dylib -needed_library legacy_leaf_x64.dylib -o legacy_unmatched_own_x64.dylib provider_x64.o
```

Clear0x100000 and replace UUID24 with LC_SUB_LIBRARY offset12/name`unmatched`,
retaining DYLD_INFO. Unlike the classic fixture, this cannot infer an ordinary
child, allowing an absent unmatched dependency to remain genuinely unvisited.
Independent `llvm-objdump --macho --private-headers legacy_unmatched_own_x64.dylib`
reported `sub_library unmatched (offset 12)` and cmdsize24. No completed
external validation command was repeated; all Simple execution stays UNRUN.
