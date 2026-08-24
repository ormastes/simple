# Any Audit Linear Classification Specification

The canonical and legacy executable specifications pin the source classifier's
observable behavior while its text assembly is linearized:

- quoted spans become the same number of spaces and preserve columns;
- unquoted comments truncate at the same byte/character position;
- cast and `is` recognition retains the historical literal-space keyword
  boundary, including the distinct tab case;
- return arrows, bracket nesting, fields, locals, parameters, and multiple
  occurrences preserve classification order;
- long prefixes are classified without constructing prefix strings.

`strip_code` retains indexed `char_at` traversal and joins collected fragments
once. Classification uses backward index checks bounded by whitespace and the
two-character keyword/arrow tokens; it does not allocate prefix slices.

The driver prints sites immediately and updates counters derived from
`ANY_CLASSES` plus a site count. It no longer retains every `AnySite` only to
rescan them for totals.

No test, build, benchmark, SPipe, or optimizer command was run for this tranche.
