# Stage-3 resume traps on macOS: hardcoded 6.5 GiB tree-RSS default + admission gate self-counts the invoking wrapper

- Status: open (workarounds documented; defaults not fixed)
- Found: 2026-11-13
- Component: `scripts/bootstrap/resume-stage3-from-admitted.sh` (Darwin RSS
  default), stage-3 memory admission gate (process scan)
- Host: macOS aarch64, 24 GiB physical, bootstrap worktree
  `/private/tmp/boot-main-20261112`

## Trap 1 — `--resume-stage3-from-admitted` dies `rss-cap-exceeded` (exit 88) on the default cap

`resume-stage3-from-admitted.sh:893` defaults the whole-program stage-3
compiler build to a hardcoded tree cap:

```sh
*-*-apple-darwin*) : "${SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB:=6835937}"; export SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB ;;
```

The documented low-memory escape hatch (`SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1`,
single-process build of the ~1651-module compiler closure) peaks at
~6.9–7.0 GiB RSS on this host — over the 6.5 GiB default. Two consecutive
resume lanes were killed at ~48 s into the parse phase:

```
status=rss-cap-exceeded  exit_status=88  max_rss_kib=6835937  peak_rss_kib=6921536
```

The kill presents as `shell=88 … class=shell-nonzero-exit`, indistinguishable
in the lane verdict from a frontend-policy error without reading
`stage3-native-build.log.rss.env`.

**Workaround:** export `SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB=11534336`
(11 GiB; the lane admits explicit caps up to the resolved ceiling — 3/4 host
RAM ≈ 18.9 GiB here) before the resume.

**Fix direction:** the Darwin default should be derived from host RAM
(e.g. `max(6835937, host_kib/3)`) or at least bounded below by the observed
whole-program stage-3 working set; a static default under the documented
escape hatch's footprint refails on every 24 GiB-class host.

## Trap 2 — stage-3 admission gate counts the invoking wrapper as a concurrent bootstrap

The stage-3 memory-admission scan (`memory-admission.*.env`) refuses with
`concurrent heavy work (native=1 bootstrap=1)` when ANY process whose cmdline
mentions the bootstrap script is alive — including the wrapper that is
launching the lane itself:

```
process_2_kind=bootstrap
process_2_pid=94173
process_2_cmd=/bin/bash -c cd ... && sh scripts/bootstrap/bootstrap-from-scratch.sh --resume-stage3-from-admitted=...
concurrent_bootstrap_count=1
```

Launching the resume through `bash -c '… bootstrap-from-scratch.sh …'` (how
every CI wrapper and agent harness naturally invokes it) therefore always
self-refuses; the operator must route through a script file whose cmdline
does not contain the script path (e.g. `sh /tmp/run-stage3-resume.sh` with an
`exec` inside).

**Fix direction:** exclude the caller's own process group / session leader
from the concurrency scan, or match only processes whose cmdline names the
script AND whose ppid chain does not include the scanning process.

## Evidence

- Trap 1: `build/bootstrap/stage3-lane/logs/aarch64-apple-darwin/stage3-native-build.log.rss.env`
  (two independent `rss-cap-exceeded` records, peaks 6921536 / >6835937 KiB).
- Trap 2: `build/bootstrap/stage3-lane/stage3/aarch64-apple-darwin/memory-admission.94174.env`
  (self-wrapper counted as `kind=bootstrap`).
- Both traps burned ~1 h of lane time on 2026-11-13 before the resume
  proceeded with the workarounds above.
