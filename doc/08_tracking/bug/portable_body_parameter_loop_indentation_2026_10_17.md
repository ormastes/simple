# Portable-body parameter loops remain over-indented

Date: 2026-10-17
Bug: BUG-PORTABLE-BODY-PARAMETER-LOOP-INDENT-20261017
Database registration: pending; no admitted database tool available.
Status: source-confirmed syntax defect; native/parser regression UNRUN.
Affected tip:636a56d65cdd1ea9969d8c8583b7f1eeaa2beb5a.

The indentation repair c389241476d indented all three parameter rebinds alike, although two belong to free functions and one to a class method. In _portable_function_header_v1, for131 has indentation4, the rebind133 has12, and the following if134 has8. In _signature_digest_v1, for632 has4, rebind634 has12, and type_name635 has8. These extra indentation levels do not correspond to an enclosing block. The class-method loop correctly uses for8/body12 and is unchanged.

The correction aligns only the two comments and two rebind statements to indentation8 within their existing loops. No expression, type, validation condition, digest field, source ordering or API changes. Exact inverse and whitespace-normalized source proof are retained externally. No permissive parser or validation fallback is added.

Working/staged source guards and diff checks are recorded separately; source review is not runtime qualification. Existing bootstrap/native feature limits remain unchanged and no new build is authorized. An admitted future parser/portable-body fixture must exercise real parameter validation and signature hashing; no executed reproduction or broad compiler/lib/MCP/LSP PASS is claimed here.
