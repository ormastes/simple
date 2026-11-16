# Fixed configuration query DATA

Source: `test/01_unit/lib/container/configuration_inspect_query_v1_spec.spl`.
Status: **AUTHORED_NOT_RUN**, four pure source scenarios. No real owner, native
process, engine, namespace or actual image correspondence is fabricated.

1. `Select the four container variants without accepting a caller format or argv`:
   assert fixed inspect verb/format shape, exact container target, correct Linux
   versus Windows labels and identical Before/After commands. Only input variants
   project all three actual configuration boolean fields.
2. `Keep the observed image ID distinct from the container ID and repository manifest`:
   both image cases preserve full bare/prefixed config IDs and reject absent,
   short, repository, uppercase and option-like inputs. Every non-image case
   refuses an image-ID argument instead of ignoring it.
3. `Refuse an option-like or incomplete container target`: assert malformed,
   short, uppercase and NUL native IDs cannot enter the fixed container query.
4. `Exercise all three compatibility forwarders against their exact closed kinds`:
   assert existing async signatures select the correct common core/input/image
   command, including exact operation, program and argv equality. The independent
   fixed-shape assertions above constrain the shared implementation itself.

The compatibility source review must compare the extracted template literals and
validation with the actual accepted integration preimages. No passing runtime
result is claimed for these unexecuted assertions. A future genuine fresh-owner
fixture must independently prove private first-image provenance, same writer/
permit/native ID and actual full capture/terminal/retirement across all three
queries. The builder's syntactically valid DATA is not a substitute.
