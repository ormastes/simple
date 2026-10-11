# HTTP response UTF-8 boundary regression

AUTHORED_UNEXECUTED. Two actual value scenarios assert Unicode UTF-8 trailing195/169 octets with round-trip wire equality, and empty-body CRLF header termination with round-trip equality. TCP transmission and platform execution remain unqualified.

```simple
use std.spec
use std.nogc_sync_mut.http_server.types.{HttpResponse}
use std.nogc_sync_mut.http_server.response.{serialize_response}
use std.common.text_bytes.{text_to_utf8_bytes, bytes_to_text}

describe "HTTP response UTF-8 provider boundary":
    it "retains non-ASCII body bytes through the wire conversion":
        val wire = serialize_response(HttpResponse.ok("é"))
        val bytes = text_to_utf8_bytes(wire)
        expect(bytes_to_text(bytes)).to_equal(wire)
        expect(bytes[bytes.len() - 2]).to_equal(195)
        expect(bytes[bytes.len() - 1]).to_equal(169)

    it "retains an empty response body and its complete header delimiter":
        val wire = serialize_response(HttpResponse.ok(""))
        expect(wire).to_end_with("\r\n\r\n")
        expect(bytes_to_text(text_to_utf8_bytes(wire))).to_equal(wire)
```
