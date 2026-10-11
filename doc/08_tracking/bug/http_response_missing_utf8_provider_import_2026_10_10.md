# HTTP response missing UTF-8 provider import

Status: OPEN — source repair and regressions authored; execution pending.

Caret essential build with producer aa404c21c4d2435e871ac0f57903da18610b452323fe09355f86b9cdddb0a41f, source a0e3b4ff2b7aa8e3d4b7c9accc83bfc8c897dbf4, failed HIR at response.spl lines 11 and 29: std.common.base_encoding does not export text_to_bytes. That facade intentionally omits the ambiguous name. The response writer now uses the existing canonical std.common.text_bytes.text_to_utf8_bytes provider, preserving the selected HTTP/TCP implementation family and write_all semantics. No direct host calls are added.

Evidence: /home/ormastes/simple-phase4-web-a0-parallel-20261010/caret/build/failure-summary.json.
Regression: test/01_unit/lib/http_server/response_utf8_boundary_spec.spl asserts exact non-ASCII octets and empty-body framing through the provider. These tests are UNEXECUTED; they do not yet qualify TCP transmission or the essential binary.
