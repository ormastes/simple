# Streamed ELF COMDAT acceptance

Source: `test/03_system/app/compiler/feature/item4_stream_comdat_spec.spl`.
Requirements: ITEM4-REQ-003/004/009. **UNRUN**: authored manual, not generated
execution evidence. No admitted Simple runtime was invoked.

| Scenario | Observable contract |
|---|---|
| Effective undefined weak | Discarded weak definition yields zero for retained scalar/GOT references; kept weak and surviving strong replacement resolve to actual data |
| First/reversed winner | Whole local-signature group selects code, data and associated RELA; reversed input order changes 11 to 22 |
| Ordinary duplicates | Strong definitions outside COMDAT still reject and preserve output |
| Losing undefined/GOT | No live error or slot from discarded references; a supplied archive still satisfies retained undefined-record demand |
| Discarded definitions | Retained local reference rejects; loser-only global reference rejects even with later replacement archive |
| Independent archive demand | Member selected for `force_archive` retains its ordinary data while its losing group disappears |
| Generic groups | Both flags-zero groups with the same local signature remain in output |
| Tiny payload windows | Entry `x` and signature `g` permit read/name/emit limits of one and real four-byte membership-word decoding |
| Empty group | Flags-only group with removed member group flag does not defeat a later nonempty signature |
| Malformed structure | Checked flags, signature/table, membership, orphan RELA, entry-size and extent mutations reject even in losing groups |
| Quotas/cancellation | Real group scans charge the retained owner; full-job failures preserve destination sentinel |

Eleven scenarios inspect actual published bytes and translate addresses using
PT_LOAD headers. The retained root's pointers must select the winner's data
and instruction immediates. A group-internal pointer proves associated RELA
selection; losing markers must be absent. Fast linker parity is not claimed.

Fixture reproduction requires the directory containing the bare `.include`
paths:

```sh
cd test/fixtures/linker/elf
clang --target=x86_64-unknown-linux-gnu -c stream_comdat_*.s
llvm-ar rcs stream_comdat_missing_provider.a stream_comdat_missing_provider.o
llvm-ar rcs stream_comdat_loser_provider.a stream_comdat_loser_provider.o
llvm-ar rcs stream_comdat_archive_member.a stream_comdat_archive_member.o
llvm-readelf -g stream_comdat_a.o stream_comdat_generic_a.o stream_comdat_tiny.o
```

Fixture assembly and group inspection succeeded. GNU linker experiments in
the lane research established the distinction between final undefined errors
and archive demand. The streamed allocated-image profile omits debug sections;
it does not claim GNU behavior for emitted nonallocated debug relocations.

After runtime admission:

```text
<runtime> test test/03_system/app/compiler/feature/item4_stream_comdat_spec.spl --native
<runtime> spipe-docgen test/03_system/app/compiler/feature/item4_stream_comdat_spec.spl --output doc/06_spec --no-index
```

Secure task-specific directories isolate outputs and must become removable
after cleanup. Logical scan/output/scratch checks do not establish measured RSS,
no-swap behavior, hosted execution, or complete item 4 readiness.
