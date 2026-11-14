# LLVM semantic rows V1

<!-- codex-architecture -->

Status: compiler source implementation and one pinned object-format diagnostic;
not runtime-profile admission. Provider owner: LLVM observer lane. Compiler
owner: `backend/llvm_xray_semantic_rows.spl`; review owner: Astra trace review.
Lower-model sidecars: N/A. No LTO qualification is claimed.

`MirToLlvm.translate_module_with_entry_policy` records the actual MIR module
identity. Both real function-definition emission paths attach `!pcsections`
only for Linux functions with `xray_mode == 2`, after the emitted linkage name
has been resolved, with an i64 native integer type and x86_64/aarch64 target.
The key is that exact concrete linkage name; the owner is the MIR module name.
The latter is an owner label, not a claim of canonical loader provenance.
Concrete emitted linkage plus actual image identity is collision authority.
No runtime symbol lookup or LLVM ordinal creates identity.
Off and never-instrumented functions receive no attachment. Existing function
attributes, optimization and inlining policy are unchanged.

The metadata carries no IR pointer uses, `llvm.used`, or retention roots.
LLVM's machine emitter emits a record only for surviving functions. ELF
link-order sections follow their function through linker garbage collection.
Metadata can be lost by IR transforms; this is physical surviving-function
coverage, not a promise that every source candidate has an observable site.
Missing requested keys, duplicate keys/addresses and unresolved addresses must
fail closed. COMDAT/ICF/address aliases require unique final binding; they are
not silently coalesced by the provider.

## Byte contract

Section `simple_xray_semantic_v1`, no compression. Little-endian Linux ELF64,
small/default LLVM code model only. Values are read bytewise: the observed
ELF section alignment is **1**, despite each record length being a multiple of 8.
The observed section is allocated and writable (`WAL`, in a RW PT_LOAD).
The provider validates and copies rows into its immutable resident map; it
must not treat the source section as immutable storage.

| Offset | Field |
|---|---|
| 0 | signed i32 displacement from this field's loaded address to function |
| 4 | u32 physical function size, emitted by LLVM |
| 8 | u64 magic `0x314d535941525853` (bytes `SXRAYSM1`) |
| 16 | u32 schema = 1 |
| 20 | u32 row bytes = align8(40 + key bytes + owner bytes) |
| 24 | u32 key bytes, 1..4096 |
| 28 | u32 owner bytes, 1..1024 |
| 32 | u64 flags/reserved = 0 |
| 40 | UTF-8 key then UTF-8 owner, without NUL; zero padding to row bytes |

The provider bounds the entire section and each record (at most 8192 bytes),
validates UTF-8, checked signed address arithmetic, executable function extent,
schema, flags, lengths and padding before binding. The main-image loaded GNU
build-id identifies the image; runtime issues incarnation. No file-offset
address is treated as a loaded address. Main image only; no shared libraries.

Runtime numeric function/site IDs are generation-local indexes into the
published, immutable sorted compiler-key manifest. They are separate fields,
even in this one-site-per-function pilot. They are not LLVM IDs, are not stable
across builds, and cannot replace IDs in another existing semantic manifest.
Selection must carry the matching build and incarnation. Private binding uses
exact live `__xray_function_address` matches, with no symbol-name inference.

## Evidence and remaining qualification

The bounded diagnostic used Ubuntu Clang 18.1.3 (1ubuntu1), target
`aarch64-unknown-linux-gnu`, `-O2 -ffunction-sections -fdata-sections`; final
PIE used `--gc-sections -z start-stop-gc --build-id=sha1`. Peak observed compiler
RSS was 80376 KiB. The fixture uses a volatile effect to retain one function.
The reproducible IR fixture is
`test/fixtures/xray/xray_llvm_semantic_rows_v1.ll`. Its live function uses the
same inline attachment spelling as the compiler emitter; that spelling also
compiled successfully with Clang 18.1.3 (76960 KiB peak RSS).
An earlier constant-only fixture correctly lost all functions and all rows
after call constant folding; `noinline` alone did not guarantee a live call.

Observed: the object had one 56-byte row for each externally defined candidate,
with `R_AARCH64_PREL32` at offset 0 and SHF_LINK_ORDER to its own text section.
The IR-dead internal function had no object row. Linking removed the unused
external function and its row. The live row at VA `0x20000` contained signed
displacement `0xfffe02c8`, resolving to function VA `0x2c8`, size 24. Its
remaining bytes exactly matched the table. Artifacts were retained at
`/tmp/xray-pcsections-abi-20261114` for review, not admitted as build products.

Simple source tests and core/MCP smoke checks: **UNRUN**, due to concurrent
large builds. No full compiler/source-to-runtime qualification, x86-64 object
qualification, LTO qualification, performance admission or release claim.
Final link must preserve the loaded build-id and use start-stop GC semantics
that do not root otherwise dead functions. Missing build-id remains closed.
The CLI emitter's llc/Clang object argument owner passes no code-model override;
the observed AArch64 default emits PREL32. Larger code models and unqualified
library-backed emitters remain outside runtime admission.

Enabled compile-options hashes and native prelower identities now include
`xray-semantic-row-v1` schema identity (using their existing canonical encoders).
This prevents an older instrumented object without rows satisfying the new
request. Disabled hash and suffix encodings remain unchanged.

Primary references: [LLVM 16 PC section format](https://releases.llvm.org/16.0.0/docs/PCSectionsMetadata.html)
and [pinned LLVM 18.1.2 machine emitter](https://llvm.googlesource.com/llvm-project/+/refs/tags/llvmorg-18.1.2/llvm/lib/CodeGen/AsmPrinter/AsmPrinter.cpp).
These explain the mechanism; the concrete qualification above is only 18.1.3.
