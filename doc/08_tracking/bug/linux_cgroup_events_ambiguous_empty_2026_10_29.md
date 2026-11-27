# Linux cgroup occupancy evidence accepted malformed suffixes

Status: portable decoder corrected and tested on macOS; Linux kernel and V4
all-descendant qualification remain unverified.

The group owner must not conclude that a subtree is empty from an ambiguous
`cgroup.events` record. The original extraction ignored malformed or unknown
lines after `populated 0`. Its first proposed shared decoder also accepted an
unterminated final record, regressing the existing owner boundary.

The production decoder now accepts exactly one newline-terminated `populated`
boolean and at most one newline-terminated `frozen` boolean, in either order.
Missing, duplicated, truncated, unknown, malformed and embedded-NUL records
fail without changing the caller's output. An unknown future kernel field
requires deliberate schema admission rather than becoming empty-tree proof.
The group wrapper retains `EPROTO` for rejected observations and its existing
bounded file-read checks.

The portable C selfcheck contains 27 fixtures. Before correction, nine fixtures
failed, including every independent-review sample. The modern SSpec acceptance
scenario executes the C compiler and that real selfcheck through SOSIX; it went
from 0/1 to 1/1 under the authorized macOS P1 diagnostic interpreter (SHA-256
prefix `ddd5aa`, interpreter/no-cache/no-db/no-session-daemon/sequential/assert-ran).
Its passing assertion requires the explicit `27 checks, 0 failures` verdict.

The check is registered in the local CI manifest and the Linux V4 group admission
runner. Linux regular-file integration fixtures also cover malformed suffixes
and duplicate frozen records, but were not executed on this macOS host.
No Linux VM, Docker, kernel cgroup run, V4 capability promotion, or Phase 2
rebuild was performed. Windows Job Objects and FreeBSD reapers are separate
providers and receive no capability claim from this parser check.
