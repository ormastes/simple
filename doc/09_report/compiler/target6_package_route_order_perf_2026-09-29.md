# Target 6 package route ordering lookup

Status: focused native route unit and paired microbenchmark PASS; full compiler
qualification remains open.

The production route already builds a linked list of selected entries for
each package before archive admission. Its ordering helper nevertheless
scanned the complete module index once for every scheduled package. The
change passes those existing links to the helper, so scheduled modules are
visited directly. The unscheduled selected-module tail retains its prior
order, and the package-index route spec reports 6 examples, 0 failures in a
no-stub Stage2 native executable.

`test/05_perf/compiler/package_index_route_order_fixture.spl` constructs a
2,488-module graph with two modules per package, selects all modules, schedules
512 packages, and checks the 2,488-item result on 32 calls. The baseline
binary was compiled from `8560770bdde` before the helper change; the candidate
was compiled after it. Thirty pairs alternated run order. Each run printed
`ordered_total=79616`; external wall time and maximum RSS were collected in
`build/mini_builds/target6_route_order_perf_pairs.json`.

| Native fixture | Samples | Median wall | P95 wall | Peak RSS |
|---|---:|---:|---:|---:|
| Baseline scan | 30 | 1,945.03 ms | 1,957.45 ms | 8,792 KiB |
| Linked package walk | 30 | 28.81 ms | 36.52 ms | 8,952 KiB |

The normalized joint score is `36.52/1957.45 + 8952/8792 = 1.037`, below
the 2.0 baseline. The candidate's fixture also constructs the package links;
the baseline fixture did not, although production built those links in both
versions. This makes the measured time and RSS comparison conservative for
the candidate. The fixture is synthetic and times this route step, not a full
compile. Production graph publication, CLI cutover, and realistic native
compile time/RSS gates remain unproven.

The available Stage2 pure-Simple capsule builds native fixtures but rejects
`check` as an unknown command. The installed main `simple` identifies itself
as a Rust bootstrap seed, so it was not substituted for the required
self-hosted `check src/compiler` gate. The core runtime smoke against the
capsule stopped at `unknown command '-c'`; the MCP native smoke stopped at
`unknown command 'run'`. Those are bootstrap-tooling limitations, not PASS
results for the changed compiler route. The broad gates remain pending until
a current full pure-Simple CLI can run them.
