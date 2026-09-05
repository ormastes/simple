# String unit suffix used byte length for scalar advancement

`scan_string_unit_suffix` collected a Unicode suffix into `String`, then looped
over `suffix.len()` while `advance()` moves one Unicode scalar. A suffix such as
`_한글` therefore advanced six times for three scalars and could consume later
tokens or reach EOF incorrectly.

The implementation now uses `suffix.chars().count()` for the minimum-length
check and consumption count. A focused regression fixture verifies a typed
Unicode suffix followed by another identifier, but its test lane reached the
three-cycle cap before a clean rerun. Keep this defect open until that fixture
and branch coverage pass in a fresh session.

