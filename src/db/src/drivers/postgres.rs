//! PostgreSQL driver implementation.
//!
//! Supports:
//! - Connection strings: postgres://user:pass@host/db
//! - SSL/TLS connections
//! - Connection pooling
//!
//! Note: Uses tokio-postgres which is async, so we use a dedicated runtime.

use crate::connection::Connection;
use crate::error::{DbError, DbResult};
use crate::row::{Row, Rows};
use crate::transaction::{Transaction, TransactionExecutor};
use crate::types::SqlValue;

use parking_lot::Mutex;
use std::sync::Arc;
use tokio_postgres::{types::ToSql as PgToSql, types::Type as PgType, Client, NoTls};

/// PostgreSQL connection.
pub struct PostgresConnection {
    /// The client handle.
    client: Arc<Mutex<Client>>,
    /// Tokio runtime for async operations.
    runtime: tokio::runtime::Runtime,
}

impl PostgresConnection {
    /// Create runtime for async operations.
    fn create_runtime() -> DbResult<tokio::runtime::Runtime> {
        tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .map_err(|e| DbError::connection_failed(e.to_string()))
    }

    /// Connect to a PostgreSQL database.
    pub async fn connect(url: &str) -> DbResult<Self> {
        let runtime = Self::create_runtime()?;

        let (client, connection) = tokio_postgres::connect(url, NoTls)
            .await
            .map_err(|e| DbError::connection_failed(e.to_string()))?;

        // Spawn the connection handler in the runtime
        runtime.spawn(async move {
            if let Err(e) = connection.await {
                tracing::error!("PostgreSQL connection error: {}", e);
            }
        });

        Ok(Self {
            client: Arc::new(Mutex::new(client)),
            runtime,
        })
    }

    /// Connect synchronously (for use from Connection trait).
    pub fn connect_sync(url: &str) -> DbResult<Self> {
        let runtime = Self::create_runtime()?;

        let (client, connection) = runtime.block_on(async {
            tokio_postgres::connect(url, NoTls)
                .await
                .map_err(|e| DbError::connection_failed(e.to_string()))
        })?;

        // Spawn the connection handler
        runtime.spawn(async move {
            if let Err(e) = connection.await {
                tracing::error!("PostgreSQL connection error: {}", e);
            }
        });

        Ok(Self {
            client: Arc::new(Mutex::new(client)),
            runtime,
        })
    }

    /// Internal query implementation.
    fn query_internal(&self, sql: &str, params: &[SqlValue]) -> DbResult<Rows> {
        let client = self.client.lock();
        let pg_params = to_pg_params(params);
        let param_refs: Vec<&(dyn PgToSql + Sync)> = pg_params.iter().map(|p| p as &(dyn PgToSql + Sync)).collect();

        let result = self.runtime.block_on(async {
            let rows = client
                .query(sql, &param_refs)
                .await
                .map_err(|e| DbError::query_failed(e.to_string()))?;

            // Get column names from first row or empty
            let columns: Vec<String> = if !rows.is_empty() {
                rows[0].columns().iter().map(|c| c.name().to_string()).collect()
            } else {
                Vec::new()
            };

            // Convert rows
            let row_vec: Vec<DbResult<Row>> = rows
                .into_iter()
                .map(|row| {
                    let values: Vec<SqlValue> = row
                        .columns()
                        .iter()
                        .enumerate()
                        .map(|(i, col)| from_pg_value(&row, i, col.type_()))
                        .collect();
                    Ok(Row::new(values, columns.clone()))
                })
                .collect();

            Ok::<_, DbError>((row_vec, columns))
        })?;

        let (rows_vec, columns) = result;
        Ok(Rows::new(Box::new(rows_vec.into_iter()), columns))
    }

    /// Internal execute implementation.
    fn execute_internal(&self, sql: &str, params: &[SqlValue]) -> DbResult<u64> {
        let client = self.client.lock();
        let pg_params = to_pg_params(params);
        let param_refs: Vec<&(dyn PgToSql + Sync)> = pg_params.iter().map(|p| p as &(dyn PgToSql + Sync)).collect();

        self.runtime.block_on(async {
            client
                .execute(sql, &param_refs)
                .await
                .map_err(|e| DbError::query_failed(e.to_string()))
        })
    }
}

impl Connection for PostgresConnection {
    fn query(&self, sql: &str, params: &[SqlValue]) -> DbResult<Rows> {
        self.query_internal(sql, params)
    }

    fn execute(&self, sql: &str, params: &[SqlValue]) -> DbResult<u64> {
        self.execute_internal(sql, params)
    }

    fn begin(&self) -> DbResult<Transaction<'_>> {
        Transaction::new(self)
    }

    fn ping(&self) -> DbResult<()> {
        self.execute("SELECT 1", &[])?;
        Ok(())
    }

    fn close(&mut self) -> DbResult<()> {
        // tokio-postgres connections are automatically closed when dropped
        Ok(())
    }

    fn driver_name(&self) -> &str {
        "postgres"
    }
}

impl TransactionExecutor for PostgresConnection {
    fn execute_raw(&self, sql: &str, params: &[SqlValue]) -> DbResult<u64> {
        self.execute(sql, params)
    }

    fn query_raw(&self, sql: &str, params: &[SqlValue]) -> DbResult<Rows> {
        self.query(sql, params)
    }
}

/// PostgreSQL parameter wrapper for type erasure.
#[derive(Debug)]
enum PgParam {
    Null,
    Bool(bool),
    Int8(i64),
    Float8(f64),
    Text(String),
    Bytea(Vec<u8>),
}

impl PgToSql for PgParam {
    fn to_sql(
        &self,
        ty: &PgType,
        out: &mut tokio_postgres::types::private::BytesMut,
    ) -> Result<tokio_postgres::types::IsNull, Box<dyn std::error::Error + Sync + Send>> {
        match self {
            PgParam::Null => Ok(tokio_postgres::types::IsNull::Yes),
            PgParam::Bool(b) => b.to_sql(ty, out),
            PgParam::Int8(i) => i.to_sql(ty, out),
            PgParam::Float8(f) => f.to_sql(ty, out),
            PgParam::Text(s) => s.to_sql(ty, out),
            PgParam::Bytea(b) => b.to_sql(ty, out),
        }
    }

    fn accepts(_ty: &PgType) -> bool {
        true // Accept all types, let PostgreSQL handle conversion
    }

    tokio_postgres::types::to_sql_checked!();
}

/// Convert SqlValue slice to PostgreSQL parameters.
fn to_pg_params(params: &[SqlValue]) -> Vec<PgParam> {
    params
        .iter()
        .map(|v| match v {
            SqlValue::Null => PgParam::Null,
            SqlValue::Boolean(b) => PgParam::Bool(*b),
            SqlValue::Integer(i) => PgParam::Int8(*i),
            SqlValue::Real(f) => PgParam::Float8(*f),
            SqlValue::Text(s) => PgParam::Text(s.clone()),
            SqlValue::Blob(b) => PgParam::Bytea(b.clone()),
        })
        .collect()
}

/// Convert PostgreSQL value to SqlValue.
fn from_pg_value(row: &tokio_postgres::Row, idx: usize, ty: &PgType) -> SqlValue {
    use tokio_postgres::types::Type;

    // Try to get value based on type
    match *ty {
        Type::BOOL => row
            .try_get::<_, Option<bool>>(idx)
            .ok()
            .flatten()
            .map(SqlValue::Boolean)
            .unwrap_or(SqlValue::Null),
        Type::INT2 => row
            .try_get::<_, Option<i16>>(idx)
            .ok()
            .flatten()
            .map(|v| SqlValue::Integer(v as i64))
            .unwrap_or(SqlValue::Null),
        Type::INT4 => row
            .try_get::<_, Option<i32>>(idx)
            .ok()
            .flatten()
            .map(|v| SqlValue::Integer(v as i64))
            .unwrap_or(SqlValue::Null),
        Type::INT8 => row
            .try_get::<_, Option<i64>>(idx)
            .ok()
            .flatten()
            .map(SqlValue::Integer)
            .unwrap_or(SqlValue::Null),
        Type::FLOAT4 => row
            .try_get::<_, Option<f32>>(idx)
            .ok()
            .flatten()
            .map(|v| SqlValue::Real(v as f64))
            .unwrap_or(SqlValue::Null),
        Type::FLOAT8 => row
            .try_get::<_, Option<f64>>(idx)
            .ok()
            .flatten()
            .map(SqlValue::Real)
            .unwrap_or(SqlValue::Null),
        Type::TEXT | Type::VARCHAR | Type::CHAR | Type::NAME => row
            .try_get::<_, Option<String>>(idx)
            .ok()
            .flatten()
            .map(SqlValue::Text)
            .unwrap_or(SqlValue::Null),
        Type::BYTEA => row
            .try_get::<_, Option<Vec<u8>>>(idx)
            .ok()
            .flatten()
            .map(SqlValue::Blob)
            .unwrap_or(SqlValue::Null),
        _ => {
            // Try to get as string for unknown types
            row.try_get::<_, Option<String>>(idx)
                .ok()
                .flatten()
                .map(SqlValue::Text)
                .unwrap_or(SqlValue::Null)
        }
    }
}

// Make PostgresConnection Send + Sync
unsafe impl Send for PostgresConnection {}
unsafe impl Sync for PostgresConnection {}
