//! Eager loading support for SQP.
//!
//! Prevents N+1 query problems with preload functionality.

use std::collections::HashMap;

use crate::model::{ModelDef, Relation, RelationType};
use crate::query::Query;

/// Preload specification for eager loading.
#[derive(Debug, Clone)]
pub struct Preload {
    /// Relation name to preload.
    pub relation: String,
    /// Nested preloads.
    pub nested: Vec<Preload>,
    /// Optional condition query for the preload.
    pub condition: Option<Query>,
}

impl Preload {
    /// Create a new preload for a relation.
    pub fn new(relation: impl Into<String>) -> Self {
        Self {
            relation: relation.into(),
            nested: Vec::new(),
            condition: None,
        }
    }

    /// Add a nested preload.
    pub fn nested(mut self, preload: Preload) -> Self {
        self.nested.push(preload);
        self
    }

    /// Add a condition query for filtering the preloaded records.
    pub fn with_condition(mut self, query: Query) -> Self {
        self.condition = Some(query);
        self
    }
}

/// Parse a preload specification string.
///
/// Supports formats like:
/// - "posts" - simple relation
/// - "posts.comments" - nested relation
/// - "author,tags" - multiple relations
///
pub fn parse_preload(spec: &str) -> Vec<Preload> {
    spec.split(',')
        .map(|s| s.trim())
        .filter(|s| !s.is_empty())
        .map(|s| {
            let parts: Vec<&str> = s.split('.').collect();
            build_nested_preload(&parts)
        })
        .collect()
}

fn build_nested_preload(parts: &[&str]) -> Preload {
    if parts.is_empty() {
        return Preload::new("");
    }

    let mut preload = Preload::new(parts[0]);
    if parts.len() > 1 {
        preload = preload.nested(build_nested_preload(&parts[1..]));
    }
    preload
}

/// Preload query builder.
///
/// Generates optimized queries for eager loading relationships.
#[derive(Debug)]
pub struct PreloadBuilder<'a> {
    /// Model definition.
    model: &'a ModelDef,
    /// Primary keys to load relations for.
    primary_keys: Vec<i64>,
    /// Preloads to execute.
    preloads: Vec<Preload>,
}

impl<'a> PreloadBuilder<'a> {
    /// Create a new preload builder.
    pub fn new(model: &'a ModelDef) -> Self {
        Self {
            model,
            primary_keys: Vec::new(),
            preloads: Vec::new(),
        }
    }

    /// Set the primary keys to load relations for.
    pub fn for_ids(mut self, ids: Vec<i64>) -> Self {
        self.primary_keys = ids;
        self
    }

    /// Add preloads.
    pub fn preload(mut self, preloads: Vec<Preload>) -> Self {
        self.preloads = preloads;
        self
    }

    /// Build queries for all preloads.
    ///
    /// Returns a map of relation name to (query, params).
    pub fn build_queries(&self) -> HashMap<String, PreloadQuery> {
        let mut queries = HashMap::new();

        for preload in &self.preloads {
            if let Some(relation) = self.find_relation(&preload.relation) {
                let query = self.build_relation_query(relation, &preload.condition);
                queries.insert(
                    preload.relation.clone(),
                    PreloadQuery {
                        relation: relation.clone(),
                        query,
                        nested: self.build_nested_queries(&preload.nested, relation),
                    },
                );
            }
        }

        queries
    }

    fn find_relation(&self, name: &str) -> Option<&Relation> {
        self.model.relations.iter().find(|r| r.name == name)
    }

    fn build_relation_query(&self, relation: &Relation, condition: &Option<Query>) -> Query {
        let related_table = crate::naming::to_table_name(&relation.related_model);

        let mut query = Query::table(&related_table);

        // Add foreign key condition based on relation type
        match &relation.relation_type {
            RelationType::HasMany | RelationType::HasOne => {
                // Child records have foreign_key pointing to parent
                // e.g., posts.user_id IN (1, 2, 3)
                if !self.primary_keys.is_empty() {
                    let placeholders: Vec<String> =
                        self.primary_keys.iter().map(|_| "?".to_string()).collect();
                    query = query.where_raw(
                        format!("{} IN ({})", relation.foreign_key, placeholders.join(", ")),
                        self.primary_keys
                            .iter()
                            .map(|id| simple_db::SqlValue::Integer(*id))
                            .collect(),
                    );
                }
            }
            RelationType::BelongsTo => {
                // Parent records are looked up by id
                // We need the foreign key values from the child records
                // This is typically handled differently
            }
            RelationType::ManyToMany { join_table } => {
                // Join through the join table
                let left_key = crate::naming::to_foreign_key(&self.model.name);
                let right_key = &relation.foreign_key;
                query = query.join(
                    join_table,
                    format!("{}.id = {}.{}", related_table, join_table, right_key),
                );
                if !self.primary_keys.is_empty() {
                    let placeholders: Vec<String> =
                        self.primary_keys.iter().map(|_| "?".to_string()).collect();
                    query = query.where_raw(
                        format!(
                            "{}.{} IN ({})",
                            join_table,
                            left_key,
                            placeholders.join(", ")
                        ),
                        self.primary_keys
                            .iter()
                            .map(|id| simple_db::SqlValue::Integer(*id))
                            .collect(),
                    );
                }
            }
        }

        // Apply additional conditions if provided
        if let Some(cond_query) = condition {
            // Merge conditions from the provided query
            // Note: This is a simplified approach; full merging would need more work
            let (_, _) = cond_query.build();
        }

        query
    }

    fn build_nested_queries(
        &self,
        _nested: &[Preload],
        _parent_relation: &Relation,
    ) -> HashMap<String, PreloadQuery> {
        // Nested preloads would be built recursively
        // For now, return empty map
        HashMap::new()
    }
}

/// A preload query result.
#[derive(Debug)]
pub struct PreloadQuery {
    /// The relation being loaded.
    pub relation: Relation,
    /// The query to execute.
    pub query: Query,
    /// Nested preload queries.
    pub nested: HashMap<String, PreloadQuery>,
}

impl PreloadQuery {
    /// Build the SQL and parameters for this preload.
    pub fn build(&self) -> (String, Vec<simple_db::SqlValue>) {
        self.query.build()
    }
}

/// Group loaded records by their foreign key.
///
/// This is used to associate preloaded records with their parent records.
pub fn group_by_foreign_key<T>(
    records: Vec<T>,
    get_fk: impl Fn(&T) -> i64,
) -> HashMap<i64, Vec<T>> {
    let mut grouped: HashMap<i64, Vec<T>> = HashMap::new();
    for record in records {
        let fk = get_fk(&record);
        grouped.entry(fk).or_default().push(record);
    }
    grouped
}

/// Preload configuration.
#[derive(Debug, Clone, Default)]
pub struct PreloadConfig {
    /// Maximum batch size for IN queries.
    pub batch_size: usize,
    /// Whether to use separate queries or joins.
    pub strategy: PreloadStrategy,
}

impl PreloadConfig {
    /// Create a new config with default settings.
    pub fn new() -> Self {
        Self {
            batch_size: 1000,
            strategy: PreloadStrategy::SeparateQueries,
        }
    }

    /// Set the batch size.
    pub fn batch_size(mut self, size: usize) -> Self {
        self.batch_size = size;
        self
    }

    /// Set the preload strategy.
    pub fn strategy(mut self, strategy: PreloadStrategy) -> Self {
        self.strategy = strategy;
        self
    }
}

/// Strategy for executing preloads.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum PreloadStrategy {
    /// Use separate queries for each relation (default).
    #[default]
    SeparateQueries,
    /// Use LEFT JOINs to load in a single query.
    LeftJoin,
    /// Use subqueries.
    Subquery,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_preload_simple() {
        let preloads = parse_preload("posts");
        assert_eq!(preloads.len(), 1);
        assert_eq!(preloads[0].relation, "posts");
        assert!(preloads[0].nested.is_empty());
    }

    #[test]
    fn test_parse_preload_nested() {
        let preloads = parse_preload("posts.comments");
        assert_eq!(preloads.len(), 1);
        assert_eq!(preloads[0].relation, "posts");
        assert_eq!(preloads[0].nested.len(), 1);
        assert_eq!(preloads[0].nested[0].relation, "comments");
    }

    #[test]
    fn test_parse_preload_multiple() {
        let preloads = parse_preload("posts, tags, author");
        assert_eq!(preloads.len(), 3);
        assert_eq!(preloads[0].relation, "posts");
        assert_eq!(preloads[1].relation, "tags");
        assert_eq!(preloads[2].relation, "author");
    }

    #[test]
    fn test_preload_new() {
        let preload = Preload::new("posts")
            .nested(Preload::new("comments"))
            .nested(Preload::new("tags"));

        assert_eq!(preload.relation, "posts");
        assert_eq!(preload.nested.len(), 2);
    }

    #[test]
    fn test_group_by_foreign_key() {
        #[derive(Debug)]
        #[allow(dead_code)]
        struct Post {
            id: i64,
            user_id: i64,
        }

        let posts = vec![
            Post { id: 1, user_id: 10 },
            Post { id: 2, user_id: 10 },
            Post { id: 3, user_id: 20 },
        ];

        let grouped = group_by_foreign_key(posts, |p| p.user_id);

        assert_eq!(grouped.len(), 2);
        assert_eq!(grouped.get(&10).unwrap().len(), 2);
        assert_eq!(grouped.get(&20).unwrap().len(), 1);
    }

    #[test]
    fn test_preload_config() {
        let config = PreloadConfig::new()
            .batch_size(500)
            .strategy(PreloadStrategy::LeftJoin);

        assert_eq!(config.batch_size, 500);
        assert_eq!(config.strategy, PreloadStrategy::LeftJoin);
    }
}
