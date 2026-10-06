# Native build streaming cache warmup owner

Source: `test/01_unit/app/cli/native_build_streaming_request_owner_spec.spl`.

## honors ordinary and stage four streaming requests without bootstrap mode

The executable scenario calls the actual production `native_build_streaming_surfaces` owner through the application environment facade. It clears bootstrap mode, captures five distinct environment configurations, restores all four saved environment values before asserting, then checks default=false, ordinary explicit=true, ordinary off=false, Stage4 explicit=true and Stage4 off=false. It does not inspect source text or call a test-only policy copy.

Evidence: Phase1 immutable compiler SHA256 `0f9bfc1f7a9f6aca254755a543687d6b3d60f18b254da9441cb60e1cd3d4a2c7`, interpreter mode; one actual named example passed, zero failed/skipped/ignored, 282ms. Outer watchdog exit0, peak174896KiB under1048576KiB. Receipt and positive-count artifact: `/tmp/simple-memory-routing-owner-evidence-20261006/unit2/{rss.env,result.json}`. This is a manually maintained evidence companion, not generated native qualification.

Remaining gate: changed native producer must execute a normal-coordinator ordinary streaming build, skip unnecessary parse-cache workers, preserve source-authority and semantic rejection gates, build/run the result under the aggregate6GB bound, and supply elapsed/RSS evidence. The focused owner PASS does not prove that broader gate.
