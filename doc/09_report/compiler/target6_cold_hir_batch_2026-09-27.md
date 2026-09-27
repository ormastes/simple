# Target 6 cold HIR batch boundary (2026-09-27)

`src/compiler/80.driver/cache/cold_hir_semantic_seed_v1.spl` now offers
`cold_hir_semantic_seeds_v1` for one frozen SCV inventory. It validates the
inventory digest once and builds one source-identity lookup before processing
the HIR modules. Every input is bound to its source path, byte count, and
content digest; each seed carries the typed HIR ABI digest and canonical
deduplicated imports. Duplicate inputs and missing `.spl` sources fail closed.

The previous single-module API remains available, but using it in a loop would
re-sort and re-hash the whole inventory for each module and linearly search
the source records. Cold publication should use the batch API and pass its
seeds to a real TLDR/SMF metadata producer before calling the package-index
builder. That production wiring is still absent.

The focused interpreter spec passed 6/6 with the deployed Rust bootstrap seed,
including stale inventory, mismatched content, duplicate source, missing
source, and wide-import cases. The interpreter spec alone does not admit native
behavior or establish p95 time and max RSS. No normalized-ratio performance
verdict is claimed.

## Isolated native boundary probe

`test/fixtures/compiler/cold_hir_batch_native_probe.spl` compiled with
`SIMPLE_NO_STUB_FALLBACK=1`, Cranelift, `core-c-bootstrap`, and entry closure.
The compiler was the historical admitted pure-Simple Stage2 binary with SHA-256
`319c7bd2f4dc15a0209fc0f76b805ff27afeecb4a411f8ad68c743191f0103d9`.
The native probe (SHA-256
`e35a42f5f941fb26c2f21ed7beca6ec9db581c8fb71fdccceb944e794e2b0b60`)
printed `PASS cold_hir_batch_native_probe` and exited 0. The binary was
260,376 bytes; this one build took 92.33 seconds and peaked at 515,064 KiB;
the one probe run peaked at 1,788 KiB. Logs are under
`build/mini_builds/target6_cold_batch_native_20260927/`.

That Stage2 compiler's admission receipt names a deleted source snapshot.
The probe validates native execution of this narrow current-source boundary,
but neither the producer lineage nor the full cold publisher/entrypoints are
admitted. Single-run timings are not p95 or a matched RSS cohort.

## Paired boundary cohort

The same native fixture was extended with `single` and `batch` modes. Both
modes create 64 identical HIR/source records, perform 32 iterations, and print
the same `CHECKSUM 131072`. `single` calls the old one-module API for each
module, while `batch` validates and indexes the inventory once per iteration.
The modes ran in alternating order for 30 samples each on host `spark-f0ce`
(Linux aarch64, kernel `6.17.0-1032-nvidia`). `/usr/bin/time` measured process
elapsed time and maximum RSS, including the same fixture setup in both modes.
The exact source fixture SHA-256 is
`d47892e3ddc4e915c617342ff6d34c9e3cd7de38893420dec5c70d660198bd5b`;
the Simple batch owner SHA-256 is
`d471592a12a941fd95c6ef06276bf19fa8b7b3a5a82610dad51636ca1ea1aac4`.
The single shared native binary SHA-256 is
`b30b3581844b78d2c97ecc1a9f1611bc6fded917d6465fd913fd246ae3299b9b`.

| Mode | p50 time | p95 time | Max RSS | p95 RSS |
| --- | ---: | ---: | ---: | ---: |
| Per-module | 1,110,000 us | 1,130,000 us | 274,372 KiB | 274,360 KiB |
| Batch | 80,000 us | 90,000 us | 27,972 KiB | 27,960 KiB |

The p95 time ratio is `0.079646`, the maximum-RSS ratio is `0.101949`, and
their normalized sum is `0.181595`. Both observed metrics improved for this
isolated boundary. All 60 outputs matched. Exact sample files are
`build/mini_builds/target6_cold_batch_native_20260927/single.samples` and
`batch.samples` (SHA-256 `d070dd788a9a26ade3746d98001fb0ff5632b919c19a9dbb5969d6f66f93a6dc`
and `e78fdbb1baa3f52c8cc7e83a61d7f23e8db94ec861ffd5645e4457cec8ca2d4b`).

This is a diagnostic algorithm comparison under the historical Stage2 compiler.
It does not meet the plan's current-source Stage4, full-entrypoint, or hard
budget admission conditions; no Target 6 production performance PASS is claimed.

## Canonical TLDR admission follow-up

`package_tldr_header_validate_v1` previously compared only the lengths of
sorted unique imports, reverse dependents, and SCC members with the input
lists. A unique but unsorted list therefore passed and could reach the index
builder with noncanonical edge order. The validator now compares each element
with its canonical sorted position. The new three-case regression failed 1/3
before the fix and passed 3/3 afterward; the existing TLDR metadata spec
passed 5/5. This is interpreter evidence only. The prior unrelated edits in
`package_tldr_metadata.spl` were preserved.

## Isolated baseline compatibility

The isolated branch starts from committed V1 index schema. The draft
assembler written against the concurrently edited V2
`package_module_index_builder` cannot compile here because that builder and
its variant-bound schema are absent from committed HEAD. Its source and two
focused specs are preserved under `build/mini_builds/target6_pending_v2/`
outside production source and test discovery. The independent cold HIR seed,
SCC helper, and canonical TLDR fix remain in this worktree. No full
entrypoint cutover or completed Git/SCV event qualification is claimed.

## Event refresh publication correction

The committed Git/SCV bridge in `inventory_events.spl` published Git inventory
events before validating the filesystem journal. A missing, truncated, or
rewritten journal could therefore leave a newer inventory with the old cursor;
the next request rejected that mismatch before it could recover. The isolated
source now validates and translates the journal first, then publishes Git and
filesystem events as one generation through
`compile_source_inventory_apply_observed_events_v1`. A regression spec checks
that overflow rejects the batch without publishing its Git event.
The cursor write remains a separate operation, so failure between inventory
publication and cursor publication still needs a recovery protocol before the
plan's complete atomicity gate can pass.

The historical Stage2 native probe compiled this boundary, but its positive
publication run returned
`inventory-publication-failed:publish-encode-empty`. The standalone check worker
built from the same compiler reported missing module surfaces in semantic mode
and a compiler/FFI array-handle mismatch in syntax mode. Neither is a PASS
for current-source Stage4. Logs and probe artifacts are under
`build/mini_builds/{scv_observed_events_native_probe,target56_check_worker}/`.
