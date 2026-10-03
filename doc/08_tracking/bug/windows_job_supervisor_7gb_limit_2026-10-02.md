# Windows Job supervisor disagreed with the watchdog's 7 GB limit

The Perl watchdog permits `--max-rss-kib=6835937`, but the Windows C helper
rejected values above 5859375. A requested 7 GB bootstrap attempt therefore
failed before creating its workload: `session-helper-install-failed`, exit
89, root PID 0, with `invalid --supervise options` from the helper.

Align the helper's accepted upper bound with the existing watchdog bound.
The default limit is unchanged, and enforcement still applies to the whole
Job Object. 6,835,937 KiB is 6,999,999,488 bytes, conservatively below the
requested 7,000,000,000-byte limit.

## Native boundary evidence

The exact modified helper source SHA256 is
`1d28f9db91cb803086970443b339744f945fea83215f7a8fb1b200ef97437400`.
Its compiled helper SHA256 is
`fb2b272e9dd28972710f335e3aebc1a07d50b18f24afa44180d8ffc4b74b13fe`.

- At 6,835,937 KiB, the real guarded exit-zero workload completed with child
  exit 0 and `quiescent=1`.
- Direct invocation of the same C helper with otherwise valid supervisor
  options and 6,835,938 KiB exited 125 with `invalid --supervise options`.
  This checks the helper boundary, not only the Perl precheck.

Receipts are retained under
`D:/dev/bootstrap-phase2-selective-windows/guard-7g-probe/`:
`guard.env`, `guard.env.process-tree.env`, and `above-max.stderr.log`.
The failed original launch is preserved separately. These checks establish
limit admission and upper-bound rejection; they do not establish a passing
hello compilation or completion of Phase3/4.
