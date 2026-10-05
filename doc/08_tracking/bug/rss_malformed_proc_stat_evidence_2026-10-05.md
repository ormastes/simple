# Preserve bounded evidence for malformed Linux process records

The combined Phase2 compiler's Hello qualification stopped with watchdog exit
89, `status=rss-measurement-failed`, after `/proc/6804/stat` failed validation.
The receipt reported peak RSS 2714112 KiB below the 5859375 KiB cap and
`quiescent=1`. Evidence lives under
`/var/tmp/simple-item5-phase2-20261005/build/item5-mir-repair/hello.log`
and `hello.rss.env`. This was an observer failure, not a compiler or Hello pass.

The strict parser previously discarded the failed record. Empty reads and
ESRCH/ENOENT were already handled; the original bytes cannot be reconstructed.
Two finite native probes (3000 exit-after-open and 2000 concurrent-reap reads)
produced only valid records. They do not establish the original failure's cause.

The diagnostic now includes the complete record length and a hex encoding of
at most its first 256 bytes. It adds no retries and changes neither the parser,
reader bounds, measurement policy, nor fatal outcome. Hex keeps embedded
newlines or terminal controls from altering diagnostic structure. The proc
record contains the process comm name, not its command-line arguments.

## Verification

`scripts/test/test-rss-proc-stat-diagnostic.py` invokes the production Perl
parser with partial, embedded-newline, and 4096-byte malformed records. Before
the patch it failed because the diagnostic lacked evidence. After the patch it
passed: every malformed record remained fatal, lengths and exact prefixes
matched, and output stayed bounded. `perl -c` and `git diff --check` passed.
The green regression was not repeated for landing.

```sh
python3 scripts/test/test-rss-proc-stat-diagnostic.py
perl -c scripts/resource/process-tree-rss-watchdog.pl
```

This is a diagnostic improvement, not a claimed fix for the unreproduced
observer race. A separately supervised Hello retry uses the unchanged strict
parser and preserves existing compiler caches. Its result is not claimed here.
