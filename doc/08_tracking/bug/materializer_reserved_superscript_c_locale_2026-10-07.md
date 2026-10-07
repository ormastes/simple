# Reserved Windows device names in the C locale

The receipt path converter accepted `/c/receipt/COM¹` under `LC_ALL=C` after
literal superscript alternatives were combined into `[1-9¹²³]`. Bash matches
that bracket expression byte-wise in this locale; it does not match the entire
UTF-8 superscript character. The earlier literal alternative rejected the path.

The repair retains ASCII case-insensitive classes and ASCII digit ranges, but
uses literal alternatives for superscript 1, 2 and 3. It adds no subprocesses
to the per-component path converter and preserves lexical path spelling.

Validation: 252 behavioral checks passed against the repaired converter in
`LC_ALL=C`, covering case variants, numeric/superscript device names, extensions,
intermediate components, invalid path syntax and valid Unicode names. The same
harness rejects the original implementation at `/c/receipt/COM¹`, confirming it
detects the regression. The lexical test is wired into the existing Windows
materializer Git-batch test entrypoint.

These checks execute the actual extracted converter without creating device
paths. They establish lexical rejection, not native Windows publication safety
or whole-bootstrap qualification. Existing native destination-handle checks
remain unchanged.
