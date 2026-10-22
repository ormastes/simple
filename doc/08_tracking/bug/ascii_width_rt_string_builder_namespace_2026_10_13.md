# ASCII width conversion imports the wrong string-builder owner

Bug ID: `ascii_width_rt_string_builder_namespace_2026_10_13`.
Status: source repair verified on the explicitly selected Phase1 seed;
native parity unrun. Authoritative bug-database reconciliation pending.

`src/app/office/sheets/ascii_width.spl` imported
`common.string_builder.RtStringBuilder`. The real loader trace resolved that
import to `src/app/common/string_builder.spl`, which does not export the class.
The intended existing owner is `src/lib/common/string_builder.spl`.
Changing only the import to `std.common.string_builder.{RtStringBuilder}` fixes
the ownership error. Both compiler implementations support explicit std/lib
namespace resolution; no resolver behavior or runtime implementation changes.

The unchanged original
`test/01_unit/app/office/sheets/ascii_width_spec.spl` executed ten cases:
the baseline failed all ten with `variable RtStringBuilder not found`; the
candidate passed all ten. Coverage includes full-width letters, digits and
spaces, mixed input, CJK, supplementary Unicode, embedded NUL and empty input.
The failing baseline was preserved, and unrelated passing cases were not rerun.

Candidate exit was 0, final Windows Job active-process count 0, peak RSS 175052KiB.
All 150 traced source reads stayed within its private 169-file source closure;
all source pins remained unchanged. The logger wrote outside the source tree.
These are actual Phase1 source-case results, not native test-product results.
Whole-suite, MCP/native smoke and six-product qualification are not claimed.

## Immutable provenance

| Input or evidence | SHA-256 / Git revision |
|---|---|
| Source cut | `cce267e717684e7f87aea1603df3da7c0745258d` |
| Reviewed remote base | `83bfb3192ed7fd972d5e4350e2426aa61ca37c1c` |
| Phase1 producer | `d95807daf8725254e6737f12b0a81965ac5ae0a9236b19eedac94940bd9867f1` |
| Owner before | `1d107cdd42f495007f658e0a6e0be9a58869ebe58045063604b22c149b8dd0b9` |
| Owner after | `f724e41af6bcdc4b5553138dc53ffcb006eff4888b34c3eabc31236f0d024c6d` |
| Original spec | `8447919d3d39753d33c5ef2e8fdff5bac64e7da4bb331c9a322662a894e67269` |
| Baseline receipt | `a0f6035a1291665691d5f0248fee5041d4140034fbf00ce8f805de95417e1431` |
| Candidate receipt | `eeaaefcf5461f885f8e515de03fef74493bee1773d2fe2cf9471309c86de8cbe` |
| Candidate log | `076d77fb26dfbbe535f7a1faa5401ab7ca50421e7b28b7cb6675821e75dfc5ff` |
| Candidate source pins | `13dfd83c4b56e481535530ec321269a7179c96032f297548f2516afd06de1c36` |

The owner and original spec match the reviewed remote base byte-for-byte.
Retained local evidence is under
`build/native_probe/ascii-width-builder-namespace-20261013-sol/`, including
`CASE_REPAIR_LEDGER.jsonl`, `PROVENANCE.json`, `REMOTE_BASE_REVIEW.json` and
`confined/candidate/`. The original failing run remains under
`build/native_probe/phase1-current-whole-20261012-sol/original-ascii_width/`.
The record distinguishes authored case names/ordinals from framework IDs and
does not convert file counts, infrastructure omissions or zero-case runs to PASS.
