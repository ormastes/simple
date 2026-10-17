# Windows tagged print imports reference discarded Rust sections

Status: REPAIRED at the C export boundary; focused mixed-runtime ABI check
passed. Canonical rebuilt compiler admission and full smux verification remain
pending. Bug database registration awaits its canonical checksummed writer.

The Windows diagnostic producer SHA-256 is
`bad4c7fced5d4c945a24a3deb8f601685446a76dbbe2ace5938feeccaea1b04a9`.
The actual Hello link, after supplying its missing producer-matching LLVM
import library, failed with relocations against discarded `rt_value_print`
and `rt_value_println` sections in native-all Rust runtime cgu11. Retained
evidence is under
`D:/dev/simple-smux-bootstrap-20261016/build/smux-windows-bootstrap/diagnostic-relink/`.

Astra inspected the actual COFF sections and disassembly. Rust coalesces each
word-order alias with `rt_print` or `rt_println`; selecting the C raw-string
function discards that section. The aliases are tail calls to `rt_print_value`
and `rt_println_value`, which already resolve to the C tagged-value owner.
Two C forwarding exports beside those owners preserve the exact intended call
targets. Reversing archive order would risk using tagged-value functions for
raw-string calls and is not the repair. No printing algorithm, function ABI,
unresolved-symbol policy or existing `/FORCE:MULTIPLE` policy changed.

The regression is
`test/01_unit/runtime/tagged_print_word_order_alias_regression.c` and its
companion expected stdout file. It tests raw-pointer print separately from
tagged nil, positive/negative integers, booleans and C-created strings. It uses
the real selected constructors and both word-order aliases.

Actual mixed-runtime evidence uses the original 32 selected C translation
units, the patched integration-tree `runtime_native.c`, retained native-all
archive and pinned LLVM-C import library. C objects use native-all MSVC flags
`/c /O2 /Gy /MD /std:c11 /DSIMPLE_RUNTIME_MEMORY_OWNER=1` with matching SDK and
LLVM 23 clang-cl. `SIMPLE_CORE_C_STANDALONE` is absent. Exact source/object
hashes, linker args JSON/RSP and MAP are retained with the
`tagged-print-native-all` prefix. Link and run Job receipts both record
complete, exit 0, quiescent 1. Actual stdout equals the companion file after
CRLF normalization; stderr is empty. MAP binds all six print names to the
patched C object. Astra independently checked these receipts, output and MAP
without rerunning passing tests.

The original Hello also compiled and ran successfully with a reviewed private
shim of these exact forwarding exports: `root-hello-alias-{build,run}.job.env`,
complete, exit 0, quiescent 1, stdout `windows native hello` plus newline.
That diagnostic success does not qualify a rebuilt producer.

Earlier mixed-test recipes incorrectly enabled the standalone macro while
linking native-all, exposing unrelated Vulkan aliases sharing a discarded
host-target getter section. Correct native-all flags remove that conflict;
no Vulkan source mutation was made. Rust-created heap objects are outside
this regression: C and Rust heap layouts are not interchangeable merely
because the tagged argument has the same word size.
