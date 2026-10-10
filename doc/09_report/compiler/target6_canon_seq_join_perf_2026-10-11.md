# Target 6 canonical sequence join microbenchmark — 2026-10-11

Status: focused native PASS. This measures one cache-key encoder; it does not qualify whole-compiler startup, warm compilation, Item 5 demand loading, or Item 6 completion.

## Change

`canon_seq` in `src/compiler/00.common/cache/canonical_identity.spl` used repeated `body = body + item` on an ever-growing string. It now uses `encoded_items.join("")`. The self-hosted `rt_string_join` computes total length and copies once. The canonical `Q<count>:` prefix and item order are unchanged.

## Provenance

- Branch base: `7437ee55925`; same benchmark source SHA-256 `9c7e3644ec3865bdd8a8d9165f8d69b039afe27c0b6571cdd108f20ab7d2c903`.
- Admitted pure-Simple Stage 2 compiler SHA-256: `e0e5a6cd522d6ee86b0dbb8e7cdd88cad21b3daa39d18b65b2ce163867e0eb06`; adjacent admission status is `admitted`. No Rust seed ran.
- Both binaries used `native-build --source src/compiler --source src/lib --source test/05_perf/compiler --entry-closure --entry test/05_perf/compiler/canon_seq_bench.spl --runtime-bundle core-c-bootstrap --backend cranelift`, `SIMPLE_NO_STUB_FALLBACK=1`, and separate cold cache directories.
- Baseline source SHA-256 `55591055e319956272eba018ae02f19737e08e2dc348cdc3181bc4b612eb9670`; candidate source SHA-256 `4175878f7f21dc6b91137aaf846abafff0924b75b6854d8b5725efabfd70b11c`.
- Baseline binary SHA-256 `a5c592bad25ebf86f8229f545f3401d34a7cb5cff5551616dcf835bbf69cc14c`, 37,016 bytes; candidate SHA-256 `b2af3fa120aca336ff704973b095e8a828d96a788f9844ef3f5b084ceabca806`, 37,920 bytes. This isolated binary-size delta is not a production size cohort.

## Measurement

The benchmark encodes 4,096 ordered `canon_str` items three times per process. Every run checks empty and embedded-empty input, the large output length and prefix, and checksum `144144`. One warmup is excluded for each binary. `/usr/bin/time` records peak process RSS. Seven independent process samples were retained for each revision.

| Revision | elapsed µs samples | p95 µs | max RSS KiB |
|---|---|---:|---:|
| repeated concatenation | 94,289; 78,985; 98,423; 82,383; 92,852; 94,619; 93,009 | 98,423 | 286,880 |
| array join | 558; 426; 582; 427; 431; 546; 555 | 582 | 3,520 |

The candidate lowers p95 by 99.41% and max RSS by 98.77% in this workload. Its normalized time-plus-memory sum is `582/98423 + 3520/286880 = 0.01818` versus baseline `2.0`; both individual metrics improve. Full compiler native cohorts and matched startup/size gates remain required.
