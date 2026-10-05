# RSS watchdog truncates Linux stat records with newline process names

Status: bounded complete-record reader implemented; focused regression PASS.

The Linux watchdog used a single Perl line read for `/proc/PID/stat`. Linux
permits a newline inside the parenthesized process name. A line read therefore
truncates a valid kernel record before its numeric fields, and the watchdog
reports `malformed /proc/PID/stat`, failing observation with exit 89.

The existing parser already accepts embedded newlines with its `/s` modifier
and greedily finds the final name delimiter. The fix reads the complete record
with a 65,536-byte ceiling, rejects read errors and oversized records, and
retains the existing parser and process identity/RSS field checks. An empty
record continues to represent a process that disappeared during observation.

`python3 scripts/test/test-rss-proc-stat-record.py` passed on Linux. The fixture
sets its own kernel process name through `prctl` to ordinary text and then
`rss\n) tricky`, reads the real `/proc` record using the production reader and
parser extracted without modification, and checks parent/group/session IDs,
start identity and RSS. It confirms a line read truncates the newline fixture.
Malformed, empty and oversized parser-input fixtures fail closed. The original
process name is restored and temporary fixtures are removed. Perl syntax and
diff whitespace checks also passed.

A prior Linux bootstrap reported a malformed-stat observation failure, but its
raw stat record was not retained. This reproduced defect is not proof that the
same process-name condition caused that particular historical failure. No
bootstrap was restarted, no cache was changed, and no performance gain is
claimed by this patch.
