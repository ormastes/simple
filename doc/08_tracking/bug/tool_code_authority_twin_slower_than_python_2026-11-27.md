# Perf: tool-code-authority.spl twin ~3.7x slower than the Python owner

- Status: open
- Filed: 2026-11-27 (python BOTH twins lane, `work/py-both-twin-1-20261127`)
- Area: bootstrap tooling / runtime crypto surface

## Measurement

Real-size closure: `scripts/bootstrap/` + `scripts/check/lib/` at release/1.0.0
(499 members), fixture repo, Windows x86_64 host, seed `simple.exe` sha256
`a2e9dd36…a39a` interpreting the twin. Three interleaved runs:

| run | python | twin | one bare `git rev-parse` |
|---|---|---|---|
| 1 | 11.4 s | 29.5 s | 3.4 s |
| 2 | 11.4 s | 53.6 s | 11.1 s |
| 3 | 25.2 s | 42.2 s | 16.0 s |

Median: python 11.4 s, twin 42.2 s. The host was heavily contended (a bare git
spawn took 3-16 s), so absolute numbers are inflated; the ratio is the signal.

## Cause

1. The Python owner computes the git blob id (`sha1("blob <n>\0" + bytes)`)
   in-process. Simple has no native SHA-1 (only interpreted
   `std.common.crypto.sha1`, far too slow for ~500 files), so the twin spawns
   one extra `git hash-object --no-filters` (length-batched; one call today).
   On this host that spawn hashing 499 files cost ~14 s alone.
2. Interpreter startup of the twin plus its std imports (~6-8 s under load).

## Fix direction

Add a runtime-backed file digest for the git blob id (e.g. an
`rt_file_git_blob_sha1` extern beside `rt_file_hash_sha256`, with a Simple
twin per the dual-implementation rule), then drop the `git hash-object` spawn.
Run the twin from a native-compiled stage binary rather than the interpreter
once phase 3 deploys one.
