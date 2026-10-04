# Item 4 bounded execution lane

Owner/session: `/root/linker_research`, `item4-bounded-execution-20261003`.
Worktree: `C:/dev/simple-item4-linker-research-20261003`.
Branch: `work/item4-bounded-execution-20261003`.
Base and expected target: `94a16103a5baeefad8bc7688e70b43b75dcf2914`,
`origin/release/1.0`. Sidecars: N/A. Parent owns integration and wrappers.

| Slice | Source/spec status | Phase 4 evidence |
|---|---|---|
| Retained archive traversal and bounded ELF member views | Implemented; ordinary archive, truncation, borrowed handle and extent specs authored | UNRUN |
| Selected-input resolution with capped descriptors and on-demand symbol scans | Implemented for static x64; real archive provider, duplicate/undefined and quota specs authored | UNRUN |
| Layout and relocation-aware image streaming | Implemented for static x64 scalar RELA; direct/archive image equality and independent cross-window patch oracles authored | UNRUN |
| Transactional publication through real filesystem owners | Integrated private image, checked spill/replay, no-replace publication, typed cleanup outcome; collision and exact scratch boundary specs authored | UNRUN |
| Cancellation | Checked throughout scans/emission/spill/publication; early-cancel and actual-file-length mid-emission writer-state specs authored | UNRUN |
| Constrained worker, no-swap, actual RSS/accounting | Pending; parent integration required | UNRUN |
| Full architecture/format/selected semantic coverage | Pending | UNRUN |

Full lane status: **FAIL/incomplete**, not bounded-engine admission.
Source-review blocker: the language guide defines classes as value types.
Free-function mutation of `ElfStreamInputsV1` counters/selected arrays,
`ArchiveFileV1` traversal state and `RetainedFile` cursor/closed fields does not
establish caller writeback. This also affects the existing retained/spill
substrate. Explicit returned-owner or `me` transitions must be implemented and
verified end-to-end before this candidate can be described as working or its
logical quotas as enforced. The implementation rows above mean source authored,
not a proven executable path. Do not admit the candidate through the facade.

Owner repair follow-up: mutations now use `me` on named `var` receivers.
`ElfStreamWriterV1` owns both input state and retained output; private
`LinkSpillIoV1` owns input/output cursors during staging/replay. Archive array
elements are written back immediately after each advance/rewind, before an
error propagates. Stage publication and cleanup update the same stage owner;
tests retain that owner through duplicate-publication/cleanup checks. ELF section
copy mutates its retained output receiver. This repairs the identified source
shape; runtime evidence is still UNRUN. The retained-file me implementation is a
required companion dependency from the parallel retained-owner lane.
`UnsupportedBudget` remains required until the enforcing execution path exists.
Serialized metadata, input-count, window, scratch and artifact limits are not
RSS measurements. No runtime rebuild or repeated diagnostic attempt is allowed.

Implementation strategy: retain input handles, decode individual records, use
explicit capped selected-input metadata, and stream relocation patches/output.
Deterministic rescans exchange additional IO for bounded resident metadata;
this tradeoff requires later matched latency/RSS evidence, not an assumed win.
Unsupported records fail explicitly before publishing a claimed image.

The callable integration is `elf_stream_link_file_v1`, returning an actual
published ELF candidate and retained cleanup capability. It does not set native
executable permissions or route through the parent facade. Retained archive
handles outlive borrowed member views. Layout retains three segment summaries;
the writer emits a fixed 288-byte header and configurable payload windows,
including intersecting portions of cross-window relocations. Scratch admission
includes the private image plus spill and replay files concurrently.

The authored fixture oracle is independent: 12,304 bytes, entry 4,198,400,
absolute patch 4,202,496, PC-relative patches 31, 8,126 and 8,111. With 64-byte
spill frames, the simultaneous scratch boundary is 41,560 logical bytes.
No runtime observation, native execution, canonical manual generation, coverage,
RSS, latency or no-swap result is claimed. Source review is separate evidence.

Remaining implementation gates include COMMON/COMDAT/TLS/GOT/dynamic semantics,
additional ISA and object formats, constrained worker admission, native mode and
host validation, and complete selected requirement coverage. Archive GNU/BSD name
handling is authored but lacks dedicated executable scenario coverage in this
wave. The finite scan budget counts logical record work, not every OS operation.
