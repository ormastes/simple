# Direct `rt_*` use was invisible to `simple lint`

Status: fixed in source; pure-Simple bootstrap-wide acceptance remains separate.

## Reproducer

`src/app/devhub/cmd_api.spl` directly imports and calls `rt_http_request`, but
the deployed lint emitted no `RAW-RT` finding. The semantic checker inspected
only lines beginning with `extern fn`, so calls, imports, and product aliases
were structurally invisible.

## Repair

- `RAW-RT-001` diagnoses raw extern declarations.
- `RAW-RT-002` diagnoses direct imports and calls.
- `RAW-RT-003` diagnoses removed product-side `fn rt_*` aliases.
- Provider exemptions come from the same
  `scripts/check/no_direct_rt_allowlist.txt` consumed by the pre-push gate.
- A stateful lexical scan excludes comments, normal strings, and multiline
  strings while retaining exact warning/fix columns.
- Diagnostics name the semantic-wrapper route. A Safe EasyFix is offered only
  for the signature-identical `rt_process_run` to `process_run` rename when an
  exact selective import from `app.io.mod` or `std.io_runtime` is present.

## Evidence

- Rust-seed standalone source contract: PASS.
- Pure-Simple standalone source contract: PASS.
- Pure-Simple cost contract: PASS for 20,000 clean lines and 2,000 raw-call
  lines under ceilings of 1s and 3s respectively.
- Canonical shell boundary self-test: PASS 4/4.
- The original broad focused spec exhausted its three-cycle guard while its
  first two fixture strings triggered a known eager seed import scan; it is not
  cited as green. The standalone contract avoids that unrelated fixture shape.
