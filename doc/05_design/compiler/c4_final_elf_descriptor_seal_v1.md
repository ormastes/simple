# C4 final ELF descriptor seal v1

Status: implemented source; compiler execution and full SOURCE admission OPEN.
Architecture owner: `/root/recover_hir_account_authority`. Merge owner: root.

The actual LLVM/Cranelift byte emission owner validates producer-context facts,
retained local descriptor bindings, exact header/table bytes and the object's
ABS64 table relocation. Its emission seal records the object content digest,
ordered section/offset/extent records and canonical slot-table digests.
`CodegenOutput` and `CompiledModule` carry that seal. The admitted output owner
creates its output exclusively, checks emitted bytes, and retains the native
file identity. No filesystem sidecar, symbol name or caller boolean is proof.

`source_region_compile_admitted_object_v1` and
`source_region_link_admitted_objects_v1` are the bounded in-process route.
The existing path-only capsule/cache/SFFI route rejects SOURCE input/seal loss.
Ordinary artifacts retain their existing behavior. Source inputs travel to the
Linux linker through the compiler's retained `/proc/<pid>/fd/<fd>` objects,
not replaceable original paths. This does not weaken CLOEXEC or add a registry.
The actual output is also exclusively created before linker effects, checked
by native inode identity against admitted input owners, and passed to `-o` via
its retained descriptor. The same inode becomes a readonly native handle for
verification; no path reopen can substitute inspected bytes. The original
request path is checked for continued inode ownership only. SOURCE failures
never unlink that pathname, so a replacement/hard-link cannot delete an input.
Linkers that replace the descriptor rather than write it are unsupported.

The common link owner requires actual strict tool and runtime admission-owner
projections. It binds the exact executed argument vector, tool artifact,
runtime snapshot/input records and retained SOURCE input set. A tool name,
engine string or requested-strict boolean does not mint a receipt. The existing
tool owner assumes its admitted installation stays under frozen owner control;
this patch does not turn that assumption into an adversarial executable lease.

Before returning SOURCE link success, the same owner opens the actual output,
checks ELF64 little-endian ET_EXEC, resolves unique retained marker bindings,
and validates every 48-byte descriptor and complete table span and digest.
One bounded symbol-table pass builds an index containing only requested local
data markers. Subsequent descriptor checks do not rescan the file's symbols;
compact-index comparisons are charged explicitly without a hash-probe claim.
Each span must be file-backed and readable, with a unique page-rounded LOAD
mapping, and either nonwritable or fully covered by loader-rounded GNU_RELRO.
The granule comes from the existing native `rt_page_size` provider, never from
a guessed constant or ELF segment alignment. Dynamic flags must request eager
binding. Unmodeled relocations and any dynamic relocation overlapping a
descriptor/table reject admission. Final identity/content digest and exact
input/tool/execution records stay in the retained link-owned result.

All retained reads and SHA streaming use finite actual file/header/table bounds
and charge the existing invocation account before operations. Account charges
remain logical reservations, as specified by that account; no physical RSS
proof is inferred. Errors close the output owner and prevent SOURCE success.
Consumers explicitly close admitted input/final owners after their last use.
Returning only an output path refuses to discard a SOURCE result silently.

Initial qualified source route is native Linux x86-64/AArch64, external admitted
direct linker, nonPIE, unstripped output, and SOURCE units with descriptor
provenance. Existing ordinary relro/now flags are reused without a global
hardening change. PIE base/addend modeling, stripped mapping, cross-target
loader receipts, other operating systems, raw SFFI and process/cache seal
transport remain unsupported. A caller must use the retained final owner;
an output path alone is not launch authority. Full constructor/query admission,
all other C4 coverage and actual launch-owner consumption remain separate gates.

Authored negative ELF fixtures and mapping tests are not an execution PASS.
The earlier native bridge read37/write-SIGSEGV proof is independent physical
evidence; its temporary descriptor ELF was deleted and is not misrepresented
as a retained artifact or as execution of this new gate.
