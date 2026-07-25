## MCP Performance Evidence

Date: 2026-04-18
Scope: `simple verify` command path after verifier split fix

STATUS: PASS

Measurement method:
- command runner: `/usr/bin/time -f 'cmd=<name> real=%e rss_kb=%M'`
- environment: local development workspace

Warm startup samples:
- `cmd=lean-status real=0.07 rss_kb=31232`
- `cmd=lean-status real=0.07 rss_kb=31488`
- `cmd=lean-status real=0.07 rss_kb=30976`

Representative request samples:
- `cmd=full-verify real=0.09 rss_kb=31488`
- `cmd=full-verify real=0.09 rss_kb=31744`
- `cmd=full-verify real=0.09 rss_kb=31112`

Summary:
- warm startup for `bin/simple verify --lean-status` is consistently about `0.07s`
- representative request for `bin/simple verify --no-write-report` is consistently about `0.09s` for local verify scope
- max rss across sampled runs is `31744 KB`

Required evidence markers:
- warm startup: present
- representative request: present
- max rss: present
