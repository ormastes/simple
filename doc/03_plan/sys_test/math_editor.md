# LibreOffice Math Test Plan

## Requirements

- MATH-001: Existing flat expression scenarios cover MathML root, identifier,
  number, and operator output.
- MATH-002: XML-sensitive operators are escaped in generated MathML.
- MATH-003 and MATH-004: Fraction shorthand covers simple numeric arguments and
  compound numerator rows.
- MATH-005: Malformed fraction shorthand falls back to flat deterministic token
  output.
- MATH-006: Structured helper scenarios cover fraction, superscript, subscript,
  square root, and fenced groups.

## Evidence

- Unit spec: `test/01_unit/app/office/math_editor_spec.spl`
- IDE catalog system spec:
  `test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl`
- Generated manuals:
  `doc/06_spec/test/01_unit/app/office/math_editor_spec.md`
  `doc/06_spec/test/03_system/app/ide/feature/ide_office_plugin_suite_spec.md`
