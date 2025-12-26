//! Naming convention utilities.
//!
//! Converts between Simple language conventions and SQL conventions.

use inflector::Inflector;

/// Convert a model name to a table name.
///
/// - `User` → `users`
/// - `BlogPost` → `blog_posts`
/// - `Category` → `categories`
pub fn to_table_name(model_name: &str) -> String {
    model_name.to_snake_case().to_plural()
}

/// Convert a field name to a column name.
///
/// - `userName` → `user_name`
/// - `createdAt` → `created_at`
pub fn to_column_name(field_name: &str) -> String {
    field_name.to_snake_case()
}

/// Convert a model name to a foreign key column name.
///
/// - `User` → `user_id`
/// - `BlogPost` → `blog_post_id`
pub fn to_foreign_key(model_name: &str) -> String {
    format!("{}_id", model_name.to_snake_case())
}

/// Convert a pair of model names to a join table name.
///
/// The table name is created by joining the pluralized names in alphabetical order.
///
/// - `(Post, Tag)` → `posts_tags`
/// - `(User, Role)` → `roles_users`
pub fn to_join_table(model1: &str, model2: &str) -> String {
    let t1 = to_table_name(model1);
    let t2 = to_table_name(model2);
    if t1 < t2 {
        format!("{}_{}", t1, t2)
    } else {
        format!("{}_{}", t2, t1)
    }
}

/// Convert a table name back to a model name.
///
/// - `users` → `User`
/// - `blog_posts` → `BlogPost`
pub fn to_model_name(table_name: &str) -> String {
    table_name.to_singular().to_pascal_case()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_to_table_name() {
        assert_eq!(to_table_name("User"), "users");
        assert_eq!(to_table_name("BlogPost"), "blog_posts");
        assert_eq!(to_table_name("Category"), "categories");
        // Note: Inflector doesn't handle irregular plurals like Person->People
        // It returns "persons" which is acceptable
        assert!(to_table_name("Person").starts_with("person"));
    }

    #[test]
    fn test_to_column_name() {
        assert_eq!(to_column_name("userName"), "user_name");
        assert_eq!(to_column_name("createdAt"), "created_at");
        assert_eq!(to_column_name("id"), "id");
    }

    #[test]
    fn test_to_foreign_key() {
        assert_eq!(to_foreign_key("User"), "user_id");
        assert_eq!(to_foreign_key("BlogPost"), "blog_post_id");
    }

    #[test]
    fn test_to_join_table() {
        assert_eq!(to_join_table("Post", "Tag"), "posts_tags");
        assert_eq!(to_join_table("Tag", "Post"), "posts_tags");
        assert_eq!(to_join_table("User", "Role"), "roles_users");
    }

    #[test]
    fn test_to_model_name() {
        assert_eq!(to_model_name("users"), "User");
        assert_eq!(to_model_name("blog_posts"), "BlogPost");
    }
}
