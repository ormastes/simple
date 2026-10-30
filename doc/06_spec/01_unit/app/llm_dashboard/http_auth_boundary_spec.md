# Dashboard loopback authority checks

Source: test/01_unit/app/llm_dashboard/http_auth_boundary_spec.spl.
Status: NOT_RUN; authored manual, not generated execution evidence.

Three pure-helper scenarios cover exact local Host/Origin for mutations,
duplicate/folded authority headers (including read requests), and optional read
origins versus missing/invalid required origins. They do not create a server,
authenticate an operator, launch a pane or qualify a multiplexer backend.

Real process/TCP/login/session/layout/input/capture/cleanup evidence belongs to
the web dashboard system scenario. Neither a source check nor a successful
403 response counts as a passing required application feature.
