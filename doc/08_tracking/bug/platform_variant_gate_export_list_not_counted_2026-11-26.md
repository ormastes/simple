# Platform variant gate does not count names exposed through `export` lists

Date: 2026-11-26
Status: fixed (2026-11-27)
Component: `scripts/check/check-platform-variant-dirs.shs`

## Problem

The `api:` check compares public names across sibling platform variants. Its
regex now counts only `pub fn` / `pub extern fn` / `extern fn` names. A bare
`fn x` made public through an `export x` list (a legal Simple pattern, used for
example in `io/file_ops.spl`) is not counted, so a variant that drops or never
had such a name is not reported: a public-API gap through export lists is missed.

## Expected fix

- Also collect names listed in `export a, b, c` statements (and the alias target
  of `export use ... as name`) into the per-variant name set (`NM` / `ALLN`).
- Add a `--selftest` fixture: a sibling variant exposing `fn x` via `export x`
  while another variant lacks it must report one `api` offender; the same name
  present in both must report none.
- Keep the baseline count at 207 unless the new rule finds real existing gaps;
  record any newly found gaps in the baseline deliberately, not silently.

## Fix (2026-11-27)

`scripts/check/check-platform-variant-dirs.shs` now folds into the per-variant
name set (`NM` / `ALLN`): names in `export a, b, c` (including multi-line lists
continued by a trailing comma, `#` comments stripped) and the alias name of
`export use ... as name`. Plain `export use` re-exports without `as` are not
counted. Selftest gained 3 fixtures (16 -> 19): export-list-missing (exactly one
`api` offender), export-list-both (none), export-list-multiline-missing (two).
The baseline reader now ignores `#` comment lines.

Before/after on the real tree (`check-platform-variant-dirs.shs`):
- before: `FAIL — 15746 item(s) checked, 207 new/grown ... (238 current)`
  (the committed baseline holds only 32 cond/name rows, so the 200 api gaps were
  already unbaselined and red; this is the "207").
- after rule: `... 259 new/grown ... (290 current)`; 52 newly found real gaps.
- after baselining those 52: `... 207 new/grown ... (290 current)`.

Newly found gaps: 13 windows-only `_*_v1` sosix containment helpers exported via
`export` lists in `sosix/windows/containment_launch_v1.spl` etc. (`_acl_refusal_v1`,
`_admit_v1`, `_cancel_v1`, `_collect_v1`, `_lease_of_v1`, `_memory_evidence_v1`,
`_poll_v1`, `_qualify_v1`, `_reap_v1`, `_run_to_end_v1`, `_support_v1`,
`_to_lease_v1`, `_volume_serial_v1`) missing from freebsd/linux/macos/simpleos
(13 x 4 = 52). They are underscore-prefixed intra-package helpers, so arguably
not public API; recorded in the baseline deliberately with a comment naming this
bug rather than special-casing `_` names.

## Known limits (Fable review, 2026-11-27)

These forms are not counted yet. No variant directory uses them today, so they are latent, not live:
- `export use m.{u, v}` without `as`.
- A multi-line `export use m.{` brace list.
- A blank line inside a continued `export` list: it ends the list.
- `export {j, k}`.

Also: about 200 same-class `api:` gaps are still red and not baselined. The 52 `_*_v1` rows are the only frozen `api:` rows. A follow-up should either exempt `_`-prefixed names or treat every `api:` row the same way.
