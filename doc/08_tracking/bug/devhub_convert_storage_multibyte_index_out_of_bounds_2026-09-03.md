# devhub convert_storage: string index out of bounds on any non-ASCII content

- Date: 2026-09-03
- Status: OPEN
- Platform observed: Windows x86_64 (`bin/simple.exe`, tracked seed)
- Product code: `src/app/devhub/convert_storage.spl`
- Spec: `test/01_unit/app/devhub/convert_storage_multibyte_spec.spl` (5 of 6 fail)

## Repro

```sh
bin/simple.exe test test/01_unit/app/devhub/convert_storage_multibyte_spec.spl
```
Exit status (read directly, not through a pipe): 1.
`Results: 6 total, 1 passed, 5 failed`.

## Observed

Every non-ASCII example dies with a semantic runtime error, not an assertion
failure — the converter walks past the end of the string:

| example | error |
|---|---|
| café before a tag | `string index out of bounds: index is 30 but length is 30 (preview="<p>café text</p><h1>Title</h1>")` |
| CJK content | `string index out of bounds: index is 2 but length is 2` |
| em-dash inside tag content | `string index out of bounds: index is 31 but length is 31 (preview="<p>a—b</p><strong>bold</strong>")` |
| multiple multi-byte chars before a closing tag | `string index out of bounds: index is 3 but length is 3` |
| multi-byte inside a paired markdown marker | `string index out of bounds: index is 23 but length is 23 (preview="Body **bold café** text")` |

The one passing example is the explicit pure-ASCII regression guard, which is
exactly the shape of a byte-offset vs. character-index confusion: the scanner
advances by character but indexes by byte (or vice versa), so the cursor
overruns by one position per multi-byte codepoint.

## Impact

`convert_storage` is the HTML/markdown <-> Confluence storage-format converter
behind `devhub wiki` create/edit. Any page containing an accented Latin
character, CJK text, or an em-dash crashes the conversion. Since the spec that
covers this is a dedicated multibyte spec and it is fully red, the facade is
effectively ASCII-only today.

## Cross-platform note

Nothing was changed by this record. The failing code is pure string handling
with no platform calls, so it is expected to reproduce on Unix — unverified
here (no Unix host in this session).
