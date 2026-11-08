# Line ending contract

The committed `.gitattributes` explicitly sets `*.sdn text eol=lf`, overriding Windows core.autocrlf. Actual attributes for the canonical database:

```text
doc/08_tracking/bug/bug_db.sdn: text: set
doc/08_tracking/bug/bug_db.sdn: eol: lf
```

The default text reader preserves line endings: `std.io_runtime.file_read` -> `file_read_result` -> `FileTextSession.open`/`read`; the file session owner explicitly documents no normalization. `file_default_text_codec` selects the UTF-8 codec. It reads raw byte chunks and passes them through `io_text_decode` -> `external_text_decode`; valid UTF-8 with Preserve returns `bytes_to_text(bytes)`. There is no CR removal on this path. These are source-owner observations, not new runtime qualification.

The writers deliberately require the canonical exact LF header and fail closed on unexpected header bytes. A CR in a data field is different from a CRLF header. The preexisting @CR@ row fixture proves only row-tolerant claim readers, not an alternate canonical checkout format. Hash normalization preserves seal portability; it does not change the loader's literal section boundary. No newline normalization was introduced into the writer or guard.
