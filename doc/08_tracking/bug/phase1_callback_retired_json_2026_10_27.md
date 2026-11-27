# Phase 1 whole-test callback requests retired JSON output

- **ID:** `phase1_callback_retired_json_2026_10_27`
- **Status:** workaround implemented; directory calibration incomplete
- **Owner:** Phase 1 test-callback lane

## Failure

The canonical Phase 1 whole-test callback prepares
`simple test --whole --parallel --max-workers=4 --unstable --mode=interpreter --json`.
The active seed-hosted runner has retired JSON output and accepts SDN instead.
The callback therefore exits before test discovery or execution, then records
`INFRASTRUCTURE_FAILED` because its parser receives no JSON summary. This is an
infrastructure failure, not a test-suite result.

## Reproduction evidence

On source `c0b3ad911f4cb00c0f3550b05baa8d06347d17d0`, seed SHA-256
`59de8c475ac8e364ebbd082d080e435a7aaffb4606d8fbc276a5372dcb3f87e6`, the
canonical callback returned process exit 2 in 6.154 seconds. `stderr.log` ends
with `ERROR: JSON test output is retired; use --sdn or --format sdn`; stdout is
empty and the result is `INFRASTRUCTURE_FAILED` with reason
`expected one combined runner summary`. The watchdog completed and proved
quiescence under the admitted cap. Evidence is retained in
`build/phase1-spipe-calibration-20261027/whole-phase1-prepared-20261027/`.

The seed reports that JSON is retired. The canonical SDN envelope is defined in
`src/lib/nogc_sync_mut/test_runner/test_runner_output.spl`, but its current
1 MiB output limit does not scale to the full suite and the public SDN route is
not available with the current process-group retirement provider.

## Repair contract

Use the runner's supported `--format=text` output as an explicitly diagnostic
workaround. Preserve full stdout/stderr bytes and hashes, parsed per-file rows,
all category summaries, skipped/pending/cache partitions, and process status.
Reject malformed, duplicate, missing, inconsistent, zero-execution, timeout,
crash, and unrun evidence as infrastructure failures. Assertion failures count
as FAIL only when the completed process has matching failure evidence. Do not
convert skips, pending outcomes, feature gates, omissions, or errors into
passes. Whole-suite coverage remains `NOT_PROVEN` until independent inventory
is reconciled.

The workaround can be removed when the public SDN route is supported for the
whole-suite report size and the process provider implements genuine process
group retirement. Until then, the text route is diagnostic only and does not
qualify SDN transport or Phase 2/product behavior. The refreshed Phase 1
artifact and subsequent structured-evidence repairs pass focused parser and
protocol tests; complete directory/whole-route calibration remains open.
The callback's 21 host checks pass on the release-based landing checkout,
covering text category parsing, malformed/process-failure rejection, prepared
request identity, dispatch, and bounded report reading. These host checks do
not establish a completed Simple whole-suite run.
