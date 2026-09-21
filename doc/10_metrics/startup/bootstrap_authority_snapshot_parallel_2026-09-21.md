# Bootstrap authority snapshot parallel evidence

Date: 2026-09-21 (Asia/Seoul)

The bounded directory snapshot was measured over the repository's
`src/compiler_rust` tree with the same source tree, output format, host, and
working directory for both runs. The serial lane used
`SIMPLE_NATIVE_BUILD_THREADS=1`; the candidate used
`SIMPLE_NATIVE_BUILD_THREADS=10`. The candidate worker count is clamped by
the bootstrap CPU count and the hard 64-worker ceiling, then by the existing
1024-file-per-worker floor.

Command shape:

```text
/usr/bin/time -f '... wall=%e user=%U sys=%S rss=%M' \
  env SIMPLE_NATIVE_BUILD_THREADS=<1|10> sh -c \
  '. scripts/check/lib/bootstrap-stage3/authority.shs; \
   bootstrap_stage3_directory_snapshot <output> src/compiler_rust'
```

Receipt:

| lane | records | wall seconds | user seconds | system seconds | max RSS KiB |
|---|---:|---:|---:|---:|---:|
| serial, 1 worker | 43,350 | 4.28 | 3.30 | 0.91 | 28,096 |
| parallel, 10 requested | 43,350 | 1.08 | 3.76 | 1.20 | 27,568 |

Both ordered snapshots have SHA-256
`2481525a19ce1cd07605cdf317bd3b0f2e1e6e15b2ef2607b1a78197bdffbf41`.

The RSS column is the snapshot owner's `/usr/bin/time` max RSS. The bounded
worker count limits aggregate child RSS; the unit fixture applies the 32 MiB
ceiling to this owner-process metric on Linux.

Provenance: `HEAD=66ed1b291f4c4c9aa9635768dc659605f3159c45`; the measured
source/test working diff (receipt excluded) was
`7632357f5e6d8cf1542d5a742b5e68173f6636d6c945ad1a6765b4bcb0d9235b`.
This receipt is structural/behavioral performance evidence for the local
Linux host with warm filesystem cache; it is not a FreeBSD timing claim.
