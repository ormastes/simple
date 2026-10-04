# Phase4 missing formula and animation helper imports

The immutable source9737/producer776ce2 Phase4 HIR cohort recorded unresolved `col_to_letter` in the spreadsheet formula engine and unresolved `min` in the HTML renderer's animation scheduler. These are leaf import gaps, distinct from the numbered-library closure defect.

`col_to_letter(i32) -> text` already exists in the formula engine's directly imported `app.office.sheets.cell` module, but was missing from its selective import list. The formula formatter calls it for A1 column labels. The repair adds the existing owner to that list.

The animation scheduler's two deadlines are `i64`; its unqualified `min` has no imported definition. The repair explicitly imports and calls the existing pure-Simple `std.math.min_i64` owner, preserving integer precision and the existing end/overflow guards.

Six executable regression cases exercise ADDRESS Z/AA/BA boundaries and anchoring, both animation minimum branches, termination, and millisecond precision beyond exact f64 integers. Native execution is PENDING; no runtime PASS is claimed. The active source/cache/job cohort is unchanged.
