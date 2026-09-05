# UTF-32 memory-performance specification

This executable performance specification records the memory behavior of
UTF-32 little-endian roundtrip and UTF-32-to-UTF-8 conversion.

The corpus contains ASCII, Latin, Korean, Chinese, and supplementary-plane
emoji scalars. Corpus construction occurs before each measurement snapshot.

Each receipt reports input/output size, retained runtime growth, auxiliary
growth, array-capacity growth, process high-water RSS, and allocation-counter
availability. Missing runtime counters are reported as `unavailable`; zero is
not accepted as proof of allocation-free behavior.

Run with:

```text
bin/simple test test/05_perf/text_i18n/utf32_memory_perf_spec.spl --mode=interpreter --no-cache
```

Release qualification requires an isolated matched-baseline host. This spec's
generous safety ceiling catches runaway growth but is not the final regression
budget.
