# SCV source manifest membership rejects non-ASCII paths

**Bug ID:** `source_manifest_membership_unicode_byte_slice_2026_11_14`
**Status:** fixing
**Severity:** P2

## Symptom

SCV snapshot admission can reject a valid selected-source manifest when the
selected rows contain a non-ASCII path. The failure is reported as
`snapshot-source-membership-mismatch`.

## Cause

`index_of("|")` returns a UTF-8 byte offset. The ordered membership helper
used that offset with bracket slicing (`row[0:separator]`), which counts
Unicode code points. With `test/fixtures/compiled_tool_protocol/protocol café.spl`,
the extracted identity includes the pipe. The ordered check still accepts the
batch, then the merge advances past the actual inventory entry and rejects
the exact row. The pinned admitted P2 source and current release source had
the same implementation.

## Evidence

The bounded native import attempt using broad `--source test/fixtures` exited
before producing an executable with `SCV-E-ADMISSION:
snapshot-source-membership-mismatch`. The captured manifest had 14,550 rows;
the selected inventory had 46,141 entries. All rows matched in an independent
byte-oriented comparison. The manifest contained two non-ASCII identities;
simulating the source helper's byte-offset/code-point-slice path reproduced
the first false-negative at row 12,209. This is source-bound reproduction of
the helper logic and a real admission failure, not a standalone native helper
test.

## Fix and verification

Use byte-oriented `substring(0, separator)` at each separator-derived identity
extraction, and retain a regression that selects more than 32 rows so it
exercises the ordered merge path with a non-ASCII identity. The focused unit
regression is authored but unrun.

The direct native helper fixture was reviewed and accepted. Its first RED
native-build attempt used the committed private-Git input
`fde05689bdc4a5ca61a974cdd7d10c2226447460` and the admitted P2 producer
`855f48d3c9f9d915be2c8d732d4da3186caa0fb49f55ba3c780a47a1bb7efd42`, under
a 256 MiB cgroup cap and 30-second limit. The build reached native codegen for
two modules, then the user-systemd journal recorded that the scope was killed
by the OOM killer (`run-r8b3dd6a703bf42c9ae14b134b4d39b79.scope`, 2026-11-14
22:29:46 +09:00); exit status was 143 and no probe binary was produced. This
does not establish the helper's runtime RED result. At that checkpoint, no
GREEN run or retry had been performed. Captured journal lines are retained at
`doc/08_tracking/bug/evidence/source_manifest_membership_unicode_256m_journal_2026-11-14.txt`;
they were queried with `journalctl --user --since '2026-11-14 22:29:40' --until
'2026-11-14 22:30:05' --no-pager -o short-precise` and filtered to the recorded
unit name. The build log is retained at
`/tmp/scv-membership-unicode-native-red/build.log`.

Exact wrapper command:

```sh
CAP_MEM_MAX=256M CAP_REQUIRE=1 timeout --foreground 30 \
  /tmp/simple-scv-source-manifest-utf8-20261114/scripts/resource/run_capped.shs \
  env XDG_CACHE_HOME=/tmp/scv-membership-unicode-native-red/xdg-cache \
  SIMPLE_NO_STUB_FALLBACK=1 \
  /home/yoon/dev/simple-jit-free-s1-20261114/build/bootstrap/pinned-src/pinned-33bc5c6d1d80/build/bootstrap-jitfree-s1/stage3/aarch64-unknown-linux-gnu/stage2-admitted/simple \
  native-build --source src \
  --entry src/app/compiler_entrypoint/source_manifest_membership.spl \
  --entry-closure --cache-dir /tmp/scv-membership-unicode-native-red/cache \
  --runtime-bundle core-c --threads 1 \
  --output /tmp/scv-membership-unicode-native-red/probe
```

After diagnosing the cgroup OOM, the same private fixture/cache ran serially
with a 1 GiB cgroup cap and 30-second timeout. The old helper was committed
as `fde05689bdc4a5ca61a974cdd7d10c2226447460`. Native build exited 0 and
compiled both modules; the produced probe (`9325e9ad35e509ee793e7fe7305e3f92ae1d46ff720256270c5a84def62ebd7c`)
exited 1 with `FAIL: valid 34-row Unicode manifest rejected`.

Then only the three separator slices changed back to byte-oriented substring
extraction; the private-Git green input is
`adf3bfa82bb46f6c4f734ec20d5a34c512c59ec3`. It reused the same private
compile cache, built both modules uncached, and exited 0. The native probe
(`ec35792b8adc641f55a4675925e68c4d7b9acc93294c72c6b399426f9d9575f8`)
exited 0 with `PASS: 34-row Unicode manifest membership`.

The 1 GiB red and green build commands were the same apart from input commit,
log path and output name:

```sh
CAP_MEM_MAX=1G CAP_REQUIRE=1 timeout --foreground 30 \
  /tmp/simple-scv-source-manifest-utf8-20261114/scripts/resource/run_capped.shs \
  env XDG_CACHE_HOME=/tmp/scv-membership-unicode-native-red/xdg-cache \
  SIMPLE_NO_STUB_FALLBACK=1 \
  /home/yoon/dev/simple-jit-free-s1-20261114/build/bootstrap/pinned-src/pinned-33bc5c6d1d80/build/bootstrap-jitfree-s1/stage3/aarch64-unknown-linux-gnu/stage2-admitted/simple \
  native-build --source src \
  --entry src/app/compiler_entrypoint/source_manifest_membership.spl \
  --entry-closure --cache-dir /tmp/scv-membership-unicode-native-red/cache \
  --runtime-bundle core-c --threads 1 \
  --output /tmp/scv-membership-unicode-native-red/probe
```

The green run used the same command with `--output
/tmp/scv-membership-unicode-native-red/probe-green`; its captured build log is
`/tmp/scv-membership-unicode-native-red/build-green-1g.log`. Native run logs
are `run-red.log` and `run-green.log` in the same private fixture directory.

These red/green runs execute the production helper copied into the tracked
fixture, plus exact copies of the production entry type and comparator. They
qualify the helper's native behavior, not full SCV admission or the full unit
spec. The full unit SSpec and a full compiler admission build after this source
fix remain unrun. The earlier changed-scope entrywrite build used the old
helper, passed source admission, and timed out before completing codegen.
