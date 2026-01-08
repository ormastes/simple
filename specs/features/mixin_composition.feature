Feature: Mixin Composition and Interaction
  As a Simple language developer
  I want to compose multiple mixins safely
  So that I can build complex behavior from simple components

  Background:
    Given the Simple compiler is available
    And the type checker is enabled

  Scenario: Diamond composition pattern
    Given a file "diamond.smp" with content:
      """
      mixin Base:
          var id: i64

      mixin Left:
          use Base
          var left_data: String

      mixin Right:
          use Base
          var right_data: String

      class Combined:
          use Left, Right  # Should share single Base
          var own_data: String
      """
    When I compile the file
    Then compilation should succeed
    And class "Combined" should have exactly one "id" field
    And "id" field should be shared between Left and Right

  Scenario: Method override in composition
    Given a file "override.smp" with content:
      """
      mixin Logger:
          fn log(msg: String):
              println(msg)

      mixin TimestampLogger:
          use Logger
          
          fn log(msg: String):  # Override
              let time = timestamp()
              println("[{time}] {msg}")

      class Service:
          use TimestampLogger
      """
    When I compile the file
    Then compilation should succeed
    And class "Service" method "log" should use TimestampLogger version

  Scenario: Method conflict requires explicit resolution
    Given a file "method_conflict.smp" with content:
      """
      mixin Flyer:
          fn move():
              println("flying")

      mixin Walker:
          fn move():
              println("walking")

      class Bird:
          use Flyer, Walker  # Error: ambiguous 'move' method
      """
    When I compile the file
    Then compilation should fail
    And the error should mention "method 'move' defined in multiple mixins"
    And the error should suggest explicit override

  Scenario: Explicit method conflict resolution
    Given a file "resolve_conflict.smp" with content:
      """
      mixin Flyer:
          fn move():
              println("flying")

      mixin Walker:
          fn move():
              println("walking")

      class Bird:
          use Flyer, Walker
          
          fn move():  # Explicit resolution
              Flyer::move(self)  # Choose one explicitly
      """
    When I compile the file
    Then compilation should succeed

  Scenario: Mixin dependency chain
    Given a file "dependency.smp" with content:
      """
      mixin Identifiable:
          var id: i64
          fn get_id() -> i64:
              return self.id

      mixin Named:
          use Identifiable
          var name: String
          
          fn get_description() -> String:
              return "{self.name} (ID: {self.get_id()})"

      class Entity:
          use Named  # Transitively gets Identifiable
      """
    When I compile the file
    Then compilation should succeed
    And class "Entity" should have field "id"
    And class "Entity" should have field "name"
    And class "Entity" should have method "get_id"
    And class "Entity" should have method "get_description"

  Scenario: Circular mixin dependency should fail
    Given a file "circular.smp" with content:
      """
      mixin A:
          use B  # Circular
          var a: i64

      mixin B:
          use A  # Circular
          var b: i64
      """
    When I compile the file
    Then compilation should fail
    And the error should mention "circular mixin dependency"

  Scenario: Mixin with trait implementation
    Given a file "mixin_trait.smp" with content:
      """
      trait Printable:
          fn print()

      mixin Printer:
          impl Printable:
              fn print():
                  println("printing")

      class Document:
          use Printer  # Gets Printable implementation
      """
    When I compile the file
    Then compilation should succeed
    And class "Document" should implement trait "Printable"

  Scenario: Mixin requires trait implementation from class
    Given a file "require_trait.smp" with content:
      """
      trait Serialize:
          fn to_bytes() -> Vec<u8>

      mixin Cacheable where Self: Serialize:
          var cache_key: String
          
          fn save_to_cache():
              let bytes = self.to_bytes()
              cache_write(self.cache_key, bytes)

      class User:
          impl Serialize:
              fn to_bytes() -> Vec<u8>:
                  # Implementation
          
          use Cacheable  # Valid: User implements Serialize
      """
    When I compile the file
    Then compilation should succeed

  Scenario: Missing required trait implementation should fail
    Given a file "missing_trait.smp" with content:
      """
      trait Serialize:
          fn to_bytes() -> Vec<u8>

      mixin Cacheable where Self: Serialize:
          var cache_key: String

      class Item:
          use Cacheable  # Error: Item doesn't implement Serialize
      """
    When I compile the file
    Then compilation should fail
    And the error should mention "class 'Item' does not implement required trait 'Serialize'"

  Scenario: Mixin provides default trait implementation
    Given a file "default_impl.smp" with content:
      """
      trait Eq:
          fn equals(other: Self) -> bool

      mixin DefaultEq:
          var id: i64
          
          impl Eq:
              fn equals(other: Self) -> bool:
                  return self.id == other.id

      class Entity:
          use DefaultEq  # Gets both field and trait impl
      """
    When I compile the file
    Then compilation should succeed
    And class "Entity" should implement "Eq"

  Scenario: Class can override mixin trait implementation
    Given a file "override_trait.smp" with content:
      """
      trait Display:
          fn display() -> String

      mixin DefaultDisplay:
          impl Display:
              fn display() -> String:
                  return "default"

      class Custom:
          use DefaultDisplay
          
          impl Display:  # Override mixin implementation
              fn display() -> String:
                  return "custom"
      """
    When I compile the file
    Then compilation should succeed
    And class "Custom" should use custom Display implementation

  Scenario: Nested mixin composition with generics
    Given a file "nested_generic.smp" with content:
      """
      mixin Container<T>:
          var items: Vec<T>

      mixin Sorted<T> where T: Ord:
          use Container<T>
          
          fn sort():
              self.items.sort()

      class SortedList:
          use Sorted<i64>
      """
    When I compile the file
    Then compilation should succeed
    And field "items" should have type "Vec<i64>"

  Scenario: Mixin composition preserves type constraints
    Given a file "preserve_constraints.smp" with content:
      """
      mixin A<T> where T: Clone:
          var a: T

      mixin B<T> where T: Debug:
          use A<T>  # Must satisfy: T: Clone + Debug
          var b: T

      class Combined:
          use B<String>  # String must be Clone + Debug
      """
    When I compile the file
    Then compilation should succeed
    And both trait bounds should be checked for String

  Scenario: Mixin field initialization order
    Given a file "init_order.smp" with content:
      """
      mixin First:
          var first: i64 = 1

      mixin Second:
          use First
          var second: i64 = self.first + 1  # Depends on First

      class Example:
          use Second
          var third: i64 = self.second + 1  # Depends on Second
      """
    When I compile the file
    Then compilation should succeed
    And initialization order should be: First -> Second -> Example

  Scenario: Mixin with private and public members
    Given a file "visibility.smp" with content:
      """
      mixin Internal:
          var public_data: i64
          private var internal_data: String
          
          fn public_method()
          private fn internal_method()

      class Service:
          use Internal
      """
    When I compile the file
    Then compilation should succeed
    And "public_data" should be accessible outside Service
    And "internal_data" should not be accessible outside Service
    And "public_method" should be accessible outside Service
    And "internal_method" should not be accessible outside Service
