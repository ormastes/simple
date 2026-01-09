//! SDN table import/export for database data.

use crate::connection::Database;
use crate::error::{DbError, DbResult};
use crate::types::SqlValue;
use simple_sdn::{parse_file, SdnValue};
use std::fs;
use std::path::Path;

/// Export a database table to an SDN named-table file.
pub fn export_table_sdn(db: &Database, table: &str, path: &Path) -> DbResult<()> {
    let sql = format!("SELECT * FROM {}", table);
    let rows = db.query(&sql, &[])?;
    let columns = rows.columns().to_vec();
    if columns.is_empty() {
        return Err(DbError::NotFound(format!(
            "table '{}' has no columns",
            table
        )));
    }

    let row_vec = rows.collect_all()?;
    let mut sdn_rows = Vec::with_capacity(row_vec.len());
    for row in row_vec {
        let mut sdn_row = Vec::with_capacity(columns.len());
        for idx in 0..columns.len() {
            let value = row
                .get_value(idx)
                .ok_or_else(|| DbError::column_not_found(format!("index {}", idx)))?;
            sdn_row.push(sql_to_sdn(value)?);
        }
        sdn_rows.push(sdn_row);
    }

    let content = render_named_table(table, &columns, &sdn_rows);
    fs::write(path, content)?;
    Ok(())
}

/// Import a database table from an SDN named-table file.
///
/// Returns the number of inserted rows.
pub fn import_table_sdn(db: &Database, table: &str, path: &Path) -> DbResult<usize> {
    let doc = parse_file(path).map_err(|e| DbError::Driver(format!("sdn parse error: {e}")))?;
    let table_value = extract_table(&doc, table)?;
    let (fields, rows) = match table_value {
        SdnValue::Table {
            fields: Some(fields),
            rows,
            ..
        } => (fields.clone(), rows.clone()),
        SdnValue::Table { .. } => {
            return Err(DbError::type_mismatch(
                "named table with fields",
                "typed table",
            ));
        }
        other => {
            return Err(DbError::type_mismatch("table", other.type_name()));
        }
    };

    let placeholders = std::iter::repeat("?")
        .take(fields.len())
        .collect::<Vec<_>>()
        .join(", ");
    let sql = format!(
        "INSERT INTO {} ({}) VALUES ({})",
        table,
        fields.join(", "),
        placeholders
    );

    let mut inserted = 0;
    for row in rows {
        let mut params = Vec::with_capacity(row.len());
        for value in row {
            params.push(sdn_to_sql(&value)?);
        }
        db.execute(&sql, &params)?;
        inserted += 1;
    }

    Ok(inserted)
}

fn extract_table<'a>(doc: &'a SdnValue, name: &str) -> DbResult<&'a SdnValue> {
    match doc {
        SdnValue::Dict(dict) => dict
            .get(name)
            .ok_or_else(|| DbError::NotFound(format!("sdn table '{}'", name))),
        other => Err(DbError::type_mismatch("dict", other.type_name())),
    }
}

fn sql_to_sdn(value: &SqlValue) -> DbResult<SdnValue> {
    match value {
        SqlValue::Null => Ok(SdnValue::Null),
        SqlValue::Boolean(b) => Ok(SdnValue::Bool(*b)),
        SqlValue::Integer(i) => Ok(SdnValue::Int(*i)),
        SqlValue::Real(f) => Ok(SdnValue::Float(*f)),
        SqlValue::Text(s) => Ok(SdnValue::String(s.clone())),
        SqlValue::Blob(_) => Err(DbError::type_mismatch("scalar", "blob")),
    }
}

fn sdn_to_sql(value: &SdnValue) -> DbResult<SqlValue> {
    match value {
        SdnValue::Null => Ok(SqlValue::Null),
        SdnValue::Bool(b) => Ok(SqlValue::Boolean(*b)),
        SdnValue::Int(i) => Ok(SqlValue::Integer(*i)),
        SdnValue::Float(f) => Ok(SqlValue::Real(*f)),
        SdnValue::String(s) => Ok(SqlValue::Text(s.clone())),
        other => Err(DbError::type_mismatch("scalar", other.type_name())),
    }
}

fn render_named_table(name: &str, fields: &[String], rows: &[Vec<SdnValue>]) -> String {
    let mut output = String::new();
    output.push_str(name);
    output.push(' ');
    output.push('|');
    output.push_str(&fields.join(", "));
    output.push('|');
    output.push('\n');

    for row in rows {
        let values = row
            .iter()
            .map(render_sdn_value)
            .collect::<Vec<_>>()
            .join(", ");
        output.push_str("    ");
        output.push_str(&values);
        output.push('\n');
    }

    output
}

fn render_sdn_value(value: &SdnValue) -> String {
    match value {
        SdnValue::Null => "null".to_string(),
        SdnValue::Bool(b) => b.to_string(),
        SdnValue::Int(i) => i.to_string(),
        SdnValue::Float(f) => f.to_string(),
        SdnValue::String(s) => render_sdn_string(s),
        other => other.to_string(),
    }
}

fn render_sdn_string(value: &str) -> String {
    if value.contains(|c: char| c.is_whitespace() || c == ',' || c == ':' || c == '"' || c == '|') {
        format!("\"{}\"", value.replace('\\', "\\\\").replace('"', "\\\""))
    } else {
        value.to_string()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn render_named_table_formats_values() {
        let rows = vec![
            vec![SdnValue::Int(1), SdnValue::String("Alice".into())],
            vec![SdnValue::Int(2), SdnValue::String("Bob B".into())],
        ];
        let output = render_named_table("users", &vec!["id".into(), "name".into()], &rows);

        assert!(output.starts_with("users |id, name|"));
        assert!(output.contains("1, Alice"));
        assert!(output.contains("2, \"Bob B\""));
    }

    #[test]
    fn sdn_sql_round_trip_scalars() {
        let values = vec![
            SqlValue::Null,
            SqlValue::Boolean(true),
            SqlValue::Integer(42),
            SqlValue::Real(3.5),
            SqlValue::Text("hello".into()),
        ];

        for value in values {
            let sdn = sql_to_sdn(&value).unwrap();
            let back = sdn_to_sql(&sdn).unwrap();
            assert_eq!(value, back);
        }
    }
}
