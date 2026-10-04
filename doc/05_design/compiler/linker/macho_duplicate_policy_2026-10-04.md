# Mach-O deterministic duplicate policy

Frozen 2026-10-04 at `fb54131d4092053c0850ae3337fea5bde17853eb`.
Owner `/root/linker_research`, branch/session
`work/item4-macho-duplicate-docs-20261004`, isolated worktree
`C:/dev/simple-item4-stream-got-docs-20261004`. Only this design is owned here;
runtime owns source, acceptance owns tests, root owns integration and host
matrix. Sidecars N/A. All Simple execution remains UNRUN.

## Concrete caller gap

Ordinary native builders and request projection select
`NativeLinkConfig.allow_duplicate_definitions=true`. The initial strict macOS
adapter rejects that field because `macho_definitions` always errors on two
strong ordinary definitions. Removing the rejection alone would silently discard
requested policy. Flipping caller defaults would change other native link paths.
The selected change implements the requested behavior in the actual symbol
resolver, then propagates configuration through the hosted adapter.

## Frozen APIs

- `MachOHostedRequest` gains `allow_duplicate_definitions: bool = false`.
- `macho_definitions(inputs, allow_duplicate_definitions: bool = false)` keeps
  its existing result type.
- `macho_unresolved(inputs, entry, allow_duplicate_definitions: bool = false)`
  passes that parameter to `macho_definitions`.
- Hosted linking passes the request field to every archive fixed-point unresolved
  scan and final definition selection.
- The native adapter maps the real config field into the request and removes
  its unsupported-field rejection only with this implementation present.
- Existing `macho_static_link` and callers omitting the new parameter remain
  strict. No default caller setting is changed.

## Resolution contract

Selected input order, then symbol-table order, defines deterministic precedence.
Two ordinary strong definitions, including supported absolute definitions,
still produce `duplicate symbol` when policy is false. With policy true, keep
the first binding: its owner and original symbol determine the address used by
entry selection, relocations and GOT construction. Later strong definitions
must not overwrite it. This does not discard the later object's sections or
unrelated definitions and is not dead stripping.

Preserve existing Mach-O precedence in both input orders:

| Pair | Winner |
|---|---|
| strong / weak ordinary definition | strong |
| weak / weak ordinary definition | first |
| ordinary definition / tentative common | ordinary, including weak |
| tentative / tentative | existing first binding; layout independently coalesces maximum size and maximum alignment |
| strong / strong | error in strict mode; first in permissive mode |

Do not transplant ELF's common-versus-weak ranking. Local symbols resolve by
their owning object, not this external-name competition. Existing undefined
weak-reference handling remains unchanged. Unsupported symbol kinds such as
N_INDR aliases remain errors; this policy does not add dynamic weak coalescing,
export interposition, or alias equivalence.

Archive selection still uses actual unresolved demand, selects one member, and
recomputes needs. A member required for a unique symbol can also introduce a
duplicate definition. Therefore permissive policy must reach the next unresolved
scan, not just the final resolver. Unneeded archive members remain unselected;
permissive duplicate policy is not whole-archive loading. Definitions selected
before the member retain priority in permissive mode. The existing common
archive-demand behavior is not expanded in this change.

## Primary domain evidence

[LLVM Mach-O SymbolTable.cpp](https://github.com/llvm/llvm-project/blob/main/lld/MachO/SymbolTable.cpp)
models common separately and keeps an existing Defined symbol when adding
common, including weak definitions. This supports preserving the existing
Mach-O ordinary-over-common behavior rather than borrowing ELF semantics.
Its lazy archive resolution also distinguishes unresolved demand from already
defined symbols. This design retains the repository's current ordering contract,
not an assertion of complete LLD algorithm equivalence.

[Apple's ld64 manual](https://github.com/apple-oss-distributions/ld64/blob/main/doc/man/man1/ld-classic.1)
marks historical duplicate-suppression options obsolete or unsupported.
Accordingly the first-selected permissive mode is Simple's explicit native
configuration policy, not claimed support for those ld64 switches. Primary
sources inspected 2026-10-04.

## Acceptance

Use canonical `std.spec.step` and private helper prefix
`item4_macho_duplicates_`. Real assembled fixtures must encode independently
distinguishable values and relocation sites; assertions read actual linked bytes.

1. Two strong providers with values 11/22: permissive native config produces
   first-selected value; reverse order produces the other value. Assert actual
   relocated pointer/GOT target and selected data, not only plan booleans.
2. Identical inputs with strict config reject `duplicate symbol` and preserve a
   pre-existing destination sentinel. Direct hosted request omitting the new
   field and existing static API remain strict.
3. An archive member required by unique `_trigger` also defines the duplicate:
   permissive mode links, resolves trigger, and retains the earlier definition;
   strict mode fails during real archive closure. A member needed only for an
   already resolved duplicate must not be pulled merely because policy is true.
4. Weak/strong and weak/common in both orders, weak/weak, and common/common
   retain existing precedence and size/alignment behavior. Use real symbol flags
   and independently expected bytes/addresses. Do not infer ELF behavior.
5. A normal positive native configuration can keep its existing true duplicate
   default while supplying the other explicitly required macOS settings. No
   unsupported debug/strip/provider option becomes silently accepted.

Fixtures and authored manuals are not execution receipts. Full SDK `.tbd` and
dyld-cache providers, native Darwin launch/compiler execution, managed admission,
Windows/Linux/SimpleOS/FreeBSD/macOS native qualification, generated manuals,
coverage and performance gates remain open. External hosted linking stays the
default; Simple's linker remains explicit opt-in.
