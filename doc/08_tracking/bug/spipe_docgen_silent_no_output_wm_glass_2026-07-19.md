# Bug: SPipe Docgen Exits Successfully Without Producing Manual

**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

## Observed

On 2026-07-19, this command completed with exit status 0 after emitting a large
set of unrelated compiler warnings:

```text
bin/simple spipe-docgen test/03_system/app/simple_wm/feature/wm_glass_theme_host_simpleos_spec.spl --output doc/06_spec --no-index
```

The required mirrored file was not created at
`doc/06_spec/03_system/app/simple_wm/feature/wm_glass_theme_host_simpleos_spec.md`
or elsewhere under `doc/06_spec`.

## Expected

Docgen should either create the mirrored manual and print its path/stub count,
or exit nonzero with a focused parse/generation diagnostic. Exit 0 with no
artifact is unsafe because verification can mistake it for successful manual
generation.

## Reproduction Notes

The source spec exists and uses established `@manual`, `@capture`, `@inline`,
`step(...)`, and module-doc conventions. The command was run once and was not
repeated because identical retry loops are prohibited. Investigation should
first add an output-existence postcondition to the docgen CLI.

## Impact

Blocks generation of the WM glass theme system manual until fixed or until a
different canonical docgen invocation is identified. It does not justify a
hand-written manual being represented as generated evidence.

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule C: filed before 2026-07-29, no runnable repro in the record, no status line existed); closed as stale per the "too old / not valid -> close" triage policy. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification if reopened.
