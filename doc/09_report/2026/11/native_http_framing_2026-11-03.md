# Native HTTP response framing repair

The POSIX core-C HTTP client accepted incomplete chunked response bodies,
non-hex chunk size suffixes/signs/prefixes, and conflicting Content-Length
fields. The related historical Simple-language decoder record
`decode_chunked_malformed_size_silently_truncates_body_2026-08-06.md` concerns
a different owner and remains unchanged.

The repair is confined to `rt_http_decode_chunked` and
`rt_http_content_length` in `src/runtime/runtime_native.c`. Chunk sizes now
use checked hexadecimal accumulation; success requires the zero chunk and
the empty line ending the trailer section. Repeated identical Content-Length
fields remain accepted; conflicting values fail. Failure leaves caller
status/body outputs unset.

## Executed evidence

Actual `runtime_native.c` is included by
`src/runtime/test/rt_http_framing_selfcheck.c`; the harness calls
`rt_http_perform` against ephemeral loopback sockets. No provider replacement,
parser copy, compiler bootstrap, or seed runtime is used.

Command from the isolated Windows worktree (Docker uses Linux):

```
docker run --rm --network none -v C:/dev/wt/http-framing-20261103:/work -w /work gcc:14 python3 scripts/check/check-runtime-http-framing.py --output build/http-framing-after
```

The same command with `build/http-framing-before` ran before the source fix.
Both runs produced `compile.log`, `results.txt`, and the executable
`http-framing` in those directories. However, the ignored build directories
were subsequently lost after expanding sparse checkout to materialize audit
scripts. They are not available as retained host artifacts. Session tool
outputs retain the source/executable hashes below and the observed totals:
before 99 cases, 63 pass, 36 fail; after 99 cases, 99 pass, 0 fail. The
before-run output also lists the first 20 failing cases. One repair cycle;
passing checks were not repeated to recreate lost artifacts.

Recorded tool-output summary (not a reconstruction of the lost full logs):

```
functions.write_stdin session_id=46400, chunk_id=22b514, exit_code=1
cases=99 passed=63 failed=36
functions.write_stdin session_id=50312, chunk_id=0930af, exit_code=0
cases=99 passed=99 failed=0
```

The matrix includes binary bytes 00/7f/80/ff, empty/short bodies, decimal
overflow/negative/suffix lengths, identical/conflicting duplicate lengths,
valid chunk extensions and trailers, absent zero/final CRLF, malformed
hexadecimal sizes and overflow, truncated trailers, and every nonempty
proper prefix of a valid binary chunked body. Every case is sent with
write strides of 1, 7, and 4096 bytes. TCP may coalesce writes; these are
controlled sender boundaries, not a claim about every kernel recv boundary.
Valid bodies are compared byte-for-byte. Rejection requires error exit 2,
empty stdout, and a nonempty diagnostic; the C harness rejects partial
body/status publication on failure.

GCC 14.4.0 container digest:
`sha256:c84ee277183a56c8302ca9a83a91535d46eeb549fd1bee958045dbf9f5e50b7f`.

Historical SHA-256 values recorded in those tool outputs; executable hashes
cannot currently be independently re-verified because the binaries were lost:

| Artifact | Hash |
| --- | --- |
| Original runtime_native.c | `9dbcb6e1e20abb0dc4b3b9853af04b702f1cf780081c9bbfeef3eaa555347893` |
| Repaired runtime_native.c | `7104c3a352f76ad9cf5fe21d42166910f9e912a4b06caea8406d956717a5cef4` |
| C harness | `b7ec0c58529d34a06162a329d6401da26d11155e37c23b3977c53d3aa43a26f8` |
| Original executable | `5bbce0b52348d9c867cde03093e07ff80e1ea513f171140a6ef2600ae1dbe117` |
| Repaired executable | `1a2c4f9ec0ce4580b0cc337b7c89e3f6fdce66fe4686f6b1756c7f08ceff0303` |

Execution result: PASS for this native framing regression; full per-case logs
and executables were lost as disclosed above. Full self-hosted checks are
UNRUN because no admitted self-hosted runtime is available. Windows core-C
HTTP remains unsupported by its existing contract. This evidence does not
qualify TLS, redirects, timeout behavior, complete trailer/extension grammar,
Transfer-Encoding ordering, or Transfer-Encoding/Content-Length ambiguity.
