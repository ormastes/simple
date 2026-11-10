# WM archive failure discarded the previous run

Priority: P2. Source repair and direct regression verified; landing pending.

The fullscreen evidence wrapper sources
`scripts/check/lib/simpleos-wm-fullscreen/retention.shs` before resetting its
canonical run files. The old archive function ignored failed copies and returned
success when its destination directory could not be created. The following
reset then deleted the only original evidence, including a previous PASS.

## Original-boundary evidence

On release source `6d496f82c5acabc2fc52b2b78146272e664dc371`, sourcing the actual
production library with real evidence, serial, and image files demonstrated:

- A failed serial-log copy returned exit 0, printed an archive PASS status, and
  removed the canonical evidence and serial log.
- A real filesystem obstruction at the archive directory returned exit 0 and
  also removed both canonical files.

Retained local logs: `C:/dev/wt/g100-os_wm/build/retention-red.log` and
`C:/dev/wt/g100-os_wm/build/retention-red-mkdir.log`. These failures predate the
repair. Command-failure injection isolates archive error handling; it does not
simulate a successful guest, renderer, or compiler.

## Repair and recovery contract

The owner creates a unique hidden staging directory on the archive filesystem,
checks every present artifact copy and metadata write, then renames the completed
directory into a uniquely named published run. Existing archive enumeration and
pruning exclude hidden partial directories. A failed archive exits before
pruning or resetting canonical evidence. A pruning failure likewise exits before
canonical reset. Previous archived runs are never overwritten. Each completed
PASS atomically updates the hidden `.latest-pass` owner record; later failed-run
archives consult that record rather than sorting random archive names. Invalid
records fail closed. Legacy runs without a record use filesystem modification
times. Pruning orders old runs by filesystem time and preserves the recorded PASS.

An interrupted or failed archive may leave `.pending-*` diagnostic fragments.
They are not published runs and cannot count as retained PASS evidence. The
canonical files remain the authoritative original and can be retried after the
filesystem issue is corrected. Operators may inspect/remove abandoned partial
directories only after establishing no live writer owns them.

## Verification

`sh scripts/check/check-wm-evidence-retention.shs` passed eight scenarios on
Windows using Git's POSIX shell, exit 0:

| Boundary | Assertion |
|---|---|
| Archive directory cannot be created | Nonzero; canonical bytes remain |
| Serial copy fails | Nonzero; canonical/prior archive bytes remain |
| Metadata write fails | Nonzero; no incomplete published run |
| Archive rename fails | Nonzero; originals and prior archive remain |
| Copy is interrupted by TERM | Nonzero; originals remain |
| Complete archive and pruning | Published evidence/serial/image bytes match; canonical reset follows |
| Pruning fails | Nonzero; canonical and prior archive bytes remain |
| No prior run | Success without creating an archive |

The added ninth scenario was executed separately with
`sh scripts/check/check-wm-evidence-retention.shs --newest-pass-only`: the newly
published PASS survives pruning even when preexisting archive names sort later.
The full harness now includes that case. Previously green unrelated scenarios
were reused rather than repeated.

Additional owner error branches are exercised by `--extended-only`: clock
failure, staging-directory failure, a preexisting publication-name collision,
an unexpected status containing a path separator, and preserving the last PASS
when archiving a failed run. Metadata-write validation was rerun alone with
`--metadata-only` after replacing multiple metadata writes with one checked
`printf`, so an earlier failed write cannot be hidden by a later successful one.

Independent review found that protecting only the current invocation's PASS
would still permit a later failed run to prune it. The completion-record repair
adds `--completion-record-only`: sequential PASS-A/PASS-B/FAIL under a frozen
timestamp and reverse-sorting nonces, plus completion-record creation/publication
failure and invalid-record controls. `--prune-only` targets pruning failure after
the ordering change. Earlier unchanged archive-copy error evidence is retained.

The harness sources the entire production owner. It uses actual directories,
files, copy/rename operations, and byte comparisons. Its only substituted
commands inject the stated failures and suppress unrelated QEMU process cleanup;
no QEMU process exists in these fixtures. This is direct shell-owner verification,
not qualification of the seven broader WM, guest, Metal, or 8K bugs.

Provider input/output/cache-read/cache-create usage: unavailable. Comparable
cohort average and usage ratio: unavailable; no estimates are fabricated.
