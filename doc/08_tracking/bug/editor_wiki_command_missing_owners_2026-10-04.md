# Editor wiki and command owners

The frozen 9d484 early Phase 4 full-CLI run reported ten unresolved names in
`editor_ctrl_wiki.spl`: seven calls to `rt_file_write_text` and three calls to
`rt_dir_walk`. `commands.spl` also lacked its `md_buffer_content` import.
Final log SHA-256:
`0850b659da9f5a612051ed073f9062414329818219bce1f96c3f044b6be01340`.

Route wiki writes through the existing `std.io_runtime.file_write_exact` owner,
which performs one native-path-normalized runtime call and returns its boolean
status. Do not substitute `write_file`: that helper can create a missing parent
and retry, changing the existing wiki failure behavior. The existing `dir_walk`
facade likewise normalizes the host path and calls the original runtime walker.
All caller status messages, successful-write counts and error branches remain.

Import the existing app `md_dispatch.md_buffer_content` implementation explicitly
for the Markdown save diagnostic route. It already uses the same EditorBuffer
type and joins its actual lines; no substitute diagnostic implementation or new
nominal type is introduced.

Four integration cases exercise real template append, missing-parent rejection,
nested vault task updates with a non-Markdown exclusion, and Markdown command
save. Fixtures use private secure temporary roots and remove them before final
content/status assertions. These cases are authored but **UNRUN**. Source review
does not qualify the editor or the failed full-CLI cohort.
