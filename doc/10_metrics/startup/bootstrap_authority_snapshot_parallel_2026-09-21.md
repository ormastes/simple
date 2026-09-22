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

## Review correction and remaining guest evidence (2026-09-22)

Review reproduced `FAIL: newline path lost existing output mode` on
`b62cdd25c81473e19f4929d5438440f701eb12f7`. The newline fallback created a
0600 output regardless of the existing mode/umask and bypassed the bound
worker path. The repair removes that fallback, uses a NUL-delimited worker
manifest, and keeps the canonical hex-encoded record stream unchanged.
Failed worker directories now have owner-side cleanup, and partial fork
failure waits for already-started workers before returning failure.

The new `bootstrap_stage3_snapshot_path_contract_test.shs` passed after the
repair: existing 0640 permissions, umask 027 creation, newline record equality,
ancestor-symlink substitution rejection, no publication after failure, and
failed-worker cleanup. The adjusted directory snapshot streaming suite also
passed, including byte equality, mutation detection, worker caps and its
Linux 32 MiB RSS gates. Both runs set `SIMPLE_NATIVE_BUILD_THREADS=12`;
the suite intentionally requests two workers for its explicit worker fixture.
The timing table above remains historical evidence, not a measurement of the
2026-09-22 correction. Memory use remains proportional to manifest size and
worker count; per-process RSS does not establish aggregate guest peak RSS.

- [ ] FreeBSD agent: after Linux bootstrap succeeds, run
  `QEMU_CPUS=12 SIMPLE_NATIVE_BUILD_THREADS=12 sh scripts/check/check-freebsd-bootstrap-qemu.shs --smoke`
  in an isolated VM/output, preserving any already-running guest bootstrap.
- [ ] In that FreeBSD guest, run the path contract and streaming tests once,
  retaining exit codes and snapshot digests, then run the canonical wrapper
  with `--full` for bootstrap admission. Record the exact candidate commit,
  compiler hashes, phase results, guest CPU count, and logs.
- [ ] Measure serial versus 12-requested-worker wall time and aggregate peak
  RSS on the same frozen guest authority tree. Existing Linux owner/process
  RSS evidence cannot satisfy this gate.
- [ ] Investigate the currently failing PR hygiene/container CI checks; no
  platform-wide PASS is claimed from focused shell regressions.

The PR remains draft pending these guest/CI gates. No new QEMU run was started
by this focused review, to respect the Linux-first sequencing requirement.
