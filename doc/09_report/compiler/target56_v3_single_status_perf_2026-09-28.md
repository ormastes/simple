# Target 6 warm Git inventory single-status optimization (2026-09-28)

**Focused result: PASS for unchanged warm inventory only.** Replacing two
separate Git commands (`diff HEAD` and `ls-files --others`) with one porcelain
status listing reduced warm p95 by 4.0% with the same observed peak RSS. This
does not qualify the full compiler or close Target 6.

## Change and correctness

`src/app/compiler_entrypoint/inventory_events.spl` parses
`git status --porcelain=v1 --untracked-files=all --no-renames` for tracked and
untracked paths in one listing. The parser rejects unknown status bytes,
escaped/control-character paths, and malformed rows before cursor publication.
It decodes Git's unescaped quoted form for filenames containing spaces; the
native integration spec covers a Unicode path with a space.
The committed change diff still uses the refresh owner's captured HEAD.
No persistence format or public inventory behavior changed.

The admitted pure-Simple Stage2 compiler SHA-256 was
`d57b8ff1c676c0e250f76f713a5e8e5b0bbf3d91fd72741698e8fe0f26ad033c`.
No-stub, entry-closure native builds and executions passed for the porcelain
unit spec (4 examples), Unicode untracked integration spec (1 example), and
the focused Git refresh probe. The probe checks cold and unchanged warm,
tracked edit/delete, untracked create, stage transition, and delete. The
changed implementation and probe source SHA-256 values were
`92ceef9b9bead27ec1afd4272d75fa5cbd96eca0e8bf5b6a6002b2cf05d94d59`
and `f830e98a97a4e55b7d736835f3b085c1b188bddd7786e4400e291a6fe29872d0`.

## Paired native measurement

The previous V3 and optimized binaries used the same aarch64 host, Git 2.43.0,
Clang 23.1.0, one committed 1,200-source fixture with tree
`9c4f00a4f18a8f2c1e560279f7652fcecdc706bd`, and the same already admitted
V3 inventory. Thirty separate warm processes per binary alternated with order
reversed every pair. `warm_ns` measures only the refresh; process wall includes
launch and inventory readback. `/usr/bin/time` supplied peak process RSS.
The complete 60-row record is
`target56_v3_single_status_samples_2026-09-28.tsv`, SHA-256
`e7f9961966ac5c69a67468fe4a9b47da6cd13fba68a039870951d3a02f8efa98`.

| Measure | Previous V3 | Single status | Ratio |
|---|---:|---:|---:|
| Warm refresh p50 | 84.059 ms | 81.655 ms | 0.971 |
| Warm refresh p95 | 99.493 ms | 95.517 ms | 0.960 |
| Peak process RSS | 27,344 KiB | 27,344 KiB | 1.000 |
| Process wall p95 | 130.225 ms | 126.895 ms | 0.974 |
| Binary size | 249,240 B | 252,392 B | 1.013 |
| Native build peak RSS (one build) | 313,696 KiB | 325,968 KiB | 1.039 |
| Native build wall (one build) | 2.97 s | 3.16 s | 1.064 |

The warm time/RSS ratio sum is **0.960035 + 1.000000 = 1.960035**, below
the required 2.000. The paired median refresh difference is -2.288 ms; a
10,000-resample paired bootstrap 95% interval is -4.329 to -0.216 ms, and
the optimized binary was faster in 21 of 30 pairs. Previous and optimized
binary SHA-256 values are
`4ca6dd6d730dec82daaf8f11060f8b429ea622fe85612f76a09976c55b43acea`
and `e87873d712f032cc79fdaefdede065d40bfd153ac6ecaaad1759744c36c313db`.

This is one focused warm cohort. Steady RSS, startup-only timing, full CLI
latency, production-scale repositories, and release-small binary size remain
unmeasured here. The optimized binary is 3,152 bytes larger; Target 5's size
gate still needs its own matched release-small cohort. The single-build rows
do not qualify build time/RSS: both values increased and no build cohort has
established whether that change exceeds noise. Target 6 still needs
typed graph publication, full entrypoint cutover, and production qualification.
