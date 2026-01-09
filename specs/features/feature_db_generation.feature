Feature: Feature DB generation
  The feature database should generate category summaries and category tables.

  Scenario: Generate category summary and detail docs
    Given a feature database with categories:
      | id   | category       | name     |
      | 100  | Core.Lexer     | Lexer    |
      | 101  | Core.Parser    | Parser   |
      | 700  | Database       | Database |
    When I generate feature docs
    Then feature.md should link to category "Core"
    And feature.md should link to category "Core.Lexer"
    And category doc "Core" should list subcategory "Core.Lexer"
