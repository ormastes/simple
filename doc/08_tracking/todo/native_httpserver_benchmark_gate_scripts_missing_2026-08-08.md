# Native HTTPServer benchmark gate scripts never built

`.claude/skills/spipe.md` (and `doc/07_guide/infra/testing/benchmarking.md`)
describe a native HTTPServer/static-file benchmark gate built from
`scripts/check/check-native-pure-simple-goal-status.shs` plus peer wrappers
(`check-web-server-nginx-live-compare.shs`,
`check-web-server-static-external-live-compare.shs`,
`check-web-server-go-erlang-static-compare.shs`,
`check-httpserver-live-static.shs`,
`check-httpserver-static-profile-counters.shs`). None of these exist under
`scripts/check/`. The retained benchmark numbers the docs cite are real and
live at `doc/10_metrics/webserver/nginx_baseline_2026-05-27.md` and
`nginx_compare_baseline.sdn` (note: `doc/10_metrics/webserver/`, not
`doc/10_metrics/perf/` as the skill doc says), but the report file
`doc/09_report/perf/web_server_nginx_compare_2026-06-17.md` referenced
alongside them does not exist either.

# TODO: [infra][P3] Build the native HTTPServer benchmark gate scripts or drop the claim
Either implement `check-native-pure-simple-goal-status.shs` and its five peer
wrappers as an automated benchmark gate (aggregating live nginx/go/erlang
compare runs into pass/fail against the retained baseline numbers), or, if
this workflow is superseded by something else, update
`doc/07_guide/infra/testing/benchmarking.md` to stop presenting the gate as
existing tooling. `.claude/skills/spipe.md` has already been softened to
mark this as planned-not-built.
