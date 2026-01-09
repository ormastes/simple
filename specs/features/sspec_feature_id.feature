Feature: SSpec feature IDs
  The SSpec parser should capture id metadata for groups and tests.

  Scenario: Parse id attributes from sspec content
    Given a sspec source with id annotations:
      """
      #[id("700")]
      describe "Database SDN table import/export":
          #[id("700.1")]
          test "Export users table to SDN":
              assert_compiles()

          #[id("700.2")]
          test "Import users table from SDN":
              assert_compiles()
      """
    When I extract sspec ids
    Then the sspec ids should include "700"
    And the sspec ids should include "700.1"
    And the sspec ids should include "700.2"
