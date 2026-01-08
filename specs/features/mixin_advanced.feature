Feature: Advanced Mixin Scenarios
  As a Simple language developer
  I want to use mixins with advanced composition patterns
  So that I can build complex reusable components

  Background:
    Given the Simple compiler is available
    And the type checker is enabled
    And type inference is enabled

  Scenario: Mixin composition - mixin using another mixin
    Given a file "mixin_composition.smp" with content:
      """
      mixin Identifiable:
          var id: i64

      mixin Timestamped:
          use Identifiable
          var created_at: i64
          var updated_at: i64

      class User:
          use Timestamped
          var name: String
      """
    When I compile the file
    Then compilation should succeed
    And class "User" should have field "id" of type "i64"
    And class "User" should have field "created_at" of type "i64"
    And class "User" should have field "name" of type "String"

  Scenario: Diamond problem resolution
    Given a file "diamond.smp" with content:
      """
      mixin Base:
          var id: i64

      mixin Left:
          use Base
          var left_field: String

      mixin Right:
          use Base
          var right_field: String

      class Derived:
          use Left, Right
          var own_field: String
      """
    When I compile the file
    Then compilation should succeed
    And class "Derived" should have exactly one field "id"
    And the "id" field should be shared from mixin "Base"

  Scenario: Mixin with generic constraints and inference
    Given a file "constrained_generic.smp" with content:
      """
      mixin Comparable<T> where T: Ord:
          var value: T

          fn is_greater_than(other: T) -> bool:
              return self.value > other

      class NumberHolder:
          use Comparable
          
          fn double_if_positive():
              if self.is_greater_than(0):
                  self.value = self.value * 2
      """
    When I compile the file with type inference
    Then compilation should succeed
    And type parameter "T" should be inferred as "i64"

  Scenario: Mixin with associated types
    Given a file "associated_types.smp" with content:
      """
      mixin Container:
          type Item
          var items: Vec<Item>

          fn add(item: Item):
              self.items.push(item)

      class UserContainer:
          use Container where Item = User
          
          fn add_user(user: User):
              self.add(user)
      """
    When I compile the file
    Then compilation should succeed
    And associated type "Item" should resolve to "User"

  Scenario: Mixin method overriding
    Given a file "method_override.smp" with content:
      """
      mixin Printable:
          fn to_string() -> String:
              return "default"

      class User:
          use Printable
          var name: String

          fn to_string() -> String:  # Override mixin method
              return "User: " + self.name
      """
    When I compile the file
    Then compilation should succeed
    And class "User" method "to_string" should override mixin method

  Scenario: Mixin with lifetime parameters
    Given a file "lifetime_mixin.smp" with content:
      """
      mixin Borrowable<'a, T>:
          var borrowed: &'a T

          fn get_ref() -> &'a T:
              return self.borrowed
      """
    When I parse the file
    Then parsing should succeed
    And the mixin should have lifetime parameter "'a"
    And the mixin should have type parameter "T"

  Scenario: Mixin type inference with multiple constraints
    Given a file "multi_constraint.smp" with content:
      """
      mixin Processor<T> where T: Clone + Debug + Send:
          var data: Vec<T>

          fn process():
              for item in self.data:
                  let cloned = item.clone()
                  println!("{:?}", cloned)
      """
    When I parse the file
    Then parsing should succeed
    And type parameter "T" should have trait bounds "Clone", "Debug", "Send"

  Scenario: Cyclic mixin dependency should fail
    Given a file "cyclic.smp" with content:
      """
      mixin A:
          use B

      mixin B:
          use A
      """
    When I compile the file
    Then compilation should fail
    And the error should mention "cyclic mixin dependency"

  Scenario: Mixin with const generics
    Given a file "const_generic_mixin.smp" with content:
      """
      mixin FixedBuffer<T, const N: usize>:
          var buffer: [T; N]

          fn capacity() -> usize:
              return N
      """
    When I parse the file
    Then parsing should succeed
    And the mixin should have type parameter "T"
    And the mixin should have const parameter "N" of type "usize"

  Scenario: Mixin field initialization order
    Given a file "init_order.smp" with content:
      """
      mixin WithDefaults:
          var counter: i64 = 0
          var active: bool = true

      class Service:
          use WithDefaults
          var name: String = "default"

          fn new(n: String) -> Service:
              return Service { name: n }  # Mixin fields auto-initialized
      """
    When I compile the file
    Then compilation should succeed
    And mixin fields should be initialized before class constructor
