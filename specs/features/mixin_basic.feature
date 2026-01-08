Feature: Basic Mixin Declaration and Application
  As a Simple language developer
  I want to declare and use mixins to add reusable functionality to classes
  So that I can compose behavior without inheritance

  Background:
    Given the Simple compiler is available
    And the type checker is enabled

  Scenario: Declare a simple mixin with fields
    Given a file "timestamp.smp" with content:
      """
      mixin Timestamp:
          var created_at: i64
          var updated_at: i64
      """
    When I parse the file
    Then parsing should succeed
    And the AST should contain a mixin declaration "Timestamp"
    And the mixin should have 2 fields
    And field "created_at" should have type "i64"
    And field "updated_at" should have type "i64"

  Scenario: Apply a mixin to a class
    Given a file "user.smp" with content:
      """
      mixin Timestamp:
          var created_at: i64
          var updated_at: i64

      class User:
          use Timestamp
          var id: i64
          var name: String
      """
    When I compile the file
    Then compilation should succeed
    And class "User" should have field "created_at" of type "i64"
    And class "User" should have field "updated_at" of type "i64"
    And class "User" should have field "id" of type "i64"
    And class "User" should have field "name" of type "String"

  Scenario: Mixin with methods
    Given a file "auditable.smp" with content:
      """
      mixin Auditable:
          var modified_by: String
          var modified_at: i64

          fn mark_modified(user: String):
              self.modified_by = user
              self.modified_at = timestamp()
      """
    When I parse the file
    Then parsing should succeed
    And the mixin should have method "mark_modified"
    And method "mark_modified" should take 1 parameter

  Scenario: Apply mixin with methods to class
    Given a file "document.smp" with content:
      """
      mixin Auditable:
          var modified_by: String
          
          fn mark_modified(user: String):
              self.modified_by = user

      class Document:
          use Auditable
          var content: String

          fn update_content(text: String, user: String):
              self.content = text
              self.mark_modified(user)  # Method from mixin
      """
    When I compile the file
    Then compilation should succeed
    And class "Document" should have method "mark_modified"
    And class "Document" should have method "update_content"

  Scenario: Multiple mixins on one class
    Given a file "multi_mixin.smp" with content:
      """
      mixin Timestamp:
          var created_at: i64

      mixin Versioned:
          var version: i64

      class Article:
          use Timestamp, Versioned
          var title: String
      """
    When I compile the file
    Then compilation should succeed
    And class "Article" should have field "created_at" from mixin "Timestamp"
    And class "Article" should have field "version" from mixin "Versioned"
    And class "Article" should have field "title"

  Scenario: Mixin field name conflict should fail
    Given a file "conflict.smp" with content:
      """
      mixin WithId:
          var id: i64

      class User:
          use WithId
          var id: String  # Conflict with mixin field
      """
    When I compile the file
    Then compilation should fail
    And the error should mention "field 'id' already defined by mixin"

  Scenario: Duplicate mixin application should fail
    Given a file "duplicate.smp" with content:
      """
      mixin Timestamp:
          var created_at: i64

      class Item:
          use Timestamp, Timestamp  # Duplicate
      """
    When I compile the file
    Then compilation should fail
    And the error should mention "mixin 'Timestamp' applied more than once"

  Scenario: Mixin with required method
    Given a file "repository.smp" with content:
      """
      mixin Repository:
          required fn table_name() -> String

          fn find_by_id(id: i64) -> Option<Self>:
              let table = self.table_name()
              # Query database...
      """
    When I parse the file
    Then parsing should succeed
    And the mixin should have required method "table_name"

  Scenario: Class must implement required methods
    Given a file "user_repository.smp" with content:
      """
      mixin Repository:
          required fn table_name() -> String

      class UserRepo:
          use Repository

          fn table_name() -> String:
              return "users"
      """
    When I compile the file
    Then compilation should succeed

  Scenario: Missing required method should fail
    Given a file "incomplete_repo.smp" with content:
      """
      mixin Repository:
          required fn table_name() -> String

      class UserRepo:
          use Repository
          # Missing table_name() implementation
      """
    When I compile the file
    Then compilation should fail
    And the error should mention "required method 'table_name' not implemented"
