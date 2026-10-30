# Native module-scope allocator residency

Status: isolated Rust owner fix validated with the actual Rust archive and LLDB; rebuilt manager acceptance remains pending.

The 6304 manager reached the unchanged 9.5 GiB RSS guard at HIR 887/1523,
then a compatible-cache continuation reached HIR 1101 with 887 hits before the
same limit. These are resource refusals, not crashes. Header/backing-buffer
counters do not account for every allocator byte; the entire gap is not yet
attributed.

A dedicated executable linked the actual frozen Rust runtime archive. With an
active session it allocated 4096 touched arrays of 1024 slots in a module scope.
Module end reduced live allocator bytes to 157,760 but left 9,115 resident pages;
a manual malloc_trim(0), with the SAME session still active, reduced residency
to 936 pages without changing live bytes. Unrelated roots survived. This proves
one allocator-residency defect at the module boundary, not a general raw-object
ownership leak and not full manager qualification.

LLDB independently stopped at malloc_trim: the first caller was probe main,
after module end, with argument 0. The later call came from rt_session_heap_end.
The completed debugger run exited 0. Log:
`/private/tmp/buildrunner-linux-lane-20261029/lldb-module-owner/baseline-complete.log`,
SHA256 `7004c465abccfcf6cf407d87e03b3230737263bcdda9f052103f94734cfd7cfe`.
Exact allocator/RSS totals differ slightly with debugger overhead.

The fix retires Rust module-scope Vec/HashSets, completes the existing C raw
scope end, and requests glibc trimming only after success and an observed drop
of at least 16 MiB in tracked header+backing-buffer bytes. The approximate process
counter delta controls an advisory optimization only: it never decides object
ownership, admission or success. Other threads can cause a conservative missed
or extra trim; libc retains all live allocations. Tiny scopes avoid allocator
sweeps. Raw allocations are not newly adopted or freed; the v1 ownership contract
is unchanged. Non-Linux/GNU platforms retain existing behavior.

A separate structural parser diagnostic (16/64/280 fields with repeated
array-wrapped field calls) showed high parsing allocations; its cause is not
claimed fixed here. LLDB malloc breakpoints identified flat-pool serialization
and registry growth but slowed the run to a bounded timeout. No crash or complete
allocation attribution is claimed for that experiment.

## Focused validation

The original frozen Rust archive fails the new ABI fixture at the first large
scope's expected trim count (actual 0, expected 1); tiny-scope and refusal checks
before it passed. The baseline stopped with assertion status 134 and core dumps
disabled. The fixture was corrected before that run to pause before promotion;
its later post-session assertion was then corrected to respect session ownership.
Promoted module nodes survive module end but are retired with their active
session; only unrelated roots are checked after session end.

An isolated sparse checkout at b9c91 plus the two reviewed Rust-file changes
built the patched runtime without mutating the frozen producer or runtime.
Two initial setup attempts lacked compiler and counterpart ABI headers and
executed no tests. Readonly links supplied those existing inputs. The corrected
focused Rust invocation executed 1 test, passed 1, failed 0, and filtered 1452;
exit 0, peak 1,388,780 KiB under a 3 GiB enforced bound. The matching no-default-
features development archive built with exit 0 and peak 1,176,644 KiB. Both
watchdogs recorded quiescent process trees.

The actual patched archive ABI fixture passed (exit 0): tiny scope requests no
trim, large scope requests one, refused ends request none, and successful
session retirement adds one. Live-session identity and promoted/unrelated roots
are checked at their valid lifetime boundaries. Archive SHA256:
`c5ceffa0856ded0acea03271bc2ee901fbd63d709b7e8e61d835ecc2c9b4304c`.

LLDB stopped at the first trim in `rt_transient_array_scope_end`, with argument
0, before the probe's manual trim. The same allocation-shaped probe reported
8,768 resident pages while allocated, 616 at module end, and still 616 after
manual trim; live allocator bytes remained 110,192 across the latter two
snapshots. It exited 0 with the session and unrelated roots intact. Absolute
counts differ from the frozen baseline due to the development archive and
debugger; this is a boundary/ownership control, not a manager benchmark.

Evidence root: `/private/tmp/buildrunner-linux-lane-20261029/moduletrim-validation`
(container `/work/moduletrim-validation`). SHA256 logs:
- `unit.log`: `beeddf59f8fb79e1af2b5fbf5f14c79fd1bfa7dc4fe11488e16499bf4c132238`
- `archive.log`: `34dc3c94364108cff695acb6ed3ac188d43d9db4b505f3a243e1baddb0198fda`
- `abi.log`: `3b7ae82bef8abc201eba317ba322ab19ad9a4cdedd3f689c35ae590556016f32`
- `lldb-fixed.log`: `1a801cdd664667431e63a544c3abb6007ffc73795611617703ce4a93e4d1deb0`

The canonical producer/runtime rebuild, manager memory admission and actual
BuildRunner Hello remain separate pending work. No limit was increased.
