//! Transaction management.

use crate::error::{DbError, DbResult};
use crate::row::Rows;
use crate::types::SqlValue;
use std::sync::atomic::{AtomicBool, Ordering};

/// Transaction state tracker.
pub(crate) trait TransactionExecutor: Send + Sync {
    fn execute_raw(&self, sql: &str, params: &[SqlValue]) -> DbResult<u64>;
    fn query_raw(&self, sql: &str, params: &[SqlValue]) -> DbResult<Rows>;
}

/// A database transaction with automatic rollback on drop.
pub struct Transaction<'a> {
    /// Executor for running queries
    executor: &'a dyn TransactionExecutor,
    /// Whether the transaction has been finalized (committed or rolled back)
    finalized: AtomicBool,
}

impl<'a> Transaction<'a> {
    /// Create a new transaction.
    pub(crate) fn new(executor: &'a dyn TransactionExecutor) -> DbResult<Self> {
        executor.execute_raw("BEGIN", &[])?;
        Ok(Self {
            executor,
            finalized: AtomicBool::new(false),
        })
    }

    /// Execute a query that doesn't return rows.
    pub fn execute(&self, sql: &str, params: &[SqlValue]) -> DbResult<u64> {
        if self.finalized.load(Ordering::Acquire) {
            return Err(DbError::transaction_failed("Transaction already finalized"));
        }
        self.executor.execute_raw(sql, params)
    }

    /// Execute a query that returns rows.
    pub fn query(&self, sql: &str, params: &[SqlValue]) -> DbResult<Rows> {
        if self.finalized.load(Ordering::Acquire) {
            return Err(DbError::transaction_failed("Transaction already finalized"));
        }
        self.executor.query_raw(sql, params)
    }

    /// Commit the transaction.
    pub fn commit(self) -> DbResult<()> {
        if self.finalized.swap(true, Ordering::AcqRel) {
            return Err(DbError::transaction_failed("Transaction already finalized"));
        }
        self.executor.execute_raw("COMMIT", &[])?;
        Ok(())
    }

    /// Rollback the transaction.
    pub fn rollback(self) -> DbResult<()> {
        if self.finalized.swap(true, Ordering::AcqRel) {
            return Err(DbError::transaction_failed("Transaction already finalized"));
        }
        self.executor.execute_raw("ROLLBACK", &[])?;
        Ok(())
    }

    /// Create a savepoint within the transaction.
    pub fn savepoint(&self, name: &str) -> DbResult<Savepoint<'_>> {
        if self.finalized.load(Ordering::Acquire) {
            return Err(DbError::transaction_failed("Transaction already finalized"));
        }
        self.executor
            .execute_raw(&format!("SAVEPOINT {}", name), &[])?;
        Ok(Savepoint {
            executor: self.executor,
            name: name.to_string(),
            released: AtomicBool::new(false),
        })
    }
}

impl Drop for Transaction<'_> {
    fn drop(&mut self) {
        // Auto-rollback if not finalized
        if !self.finalized.swap(true, Ordering::AcqRel) {
            let _ = self.executor.execute_raw("ROLLBACK", &[]);
        }
    }
}

/// A savepoint within a transaction.
pub struct Savepoint<'a> {
    /// Executor for running queries
    executor: &'a dyn TransactionExecutor,
    /// Savepoint name
    name: String,
    /// Whether the savepoint has been released or rolled back
    released: AtomicBool,
}

impl Savepoint<'_> {
    /// Release the savepoint (keep changes).
    pub fn release(self) -> DbResult<()> {
        if self.released.swap(true, Ordering::AcqRel) {
            return Err(DbError::transaction_failed("Savepoint already released"));
        }
        self.executor
            .execute_raw(&format!("RELEASE SAVEPOINT {}", self.name), &[])?;
        Ok(())
    }

    /// Rollback to the savepoint (discard changes since savepoint).
    pub fn rollback(self) -> DbResult<()> {
        if self.released.swap(true, Ordering::AcqRel) {
            return Err(DbError::transaction_failed("Savepoint already released"));
        }
        self.executor
            .execute_raw(&format!("ROLLBACK TO SAVEPOINT {}", self.name), &[])?;
        Ok(())
    }
}

impl Drop for Savepoint<'_> {
    fn drop(&mut self) {
        // Release savepoint if not already done
        if !self.released.swap(true, Ordering::AcqRel) {
            let _ = self
                .executor
                .execute_raw(&format!("RELEASE SAVEPOINT {}", self.name), &[]);
        }
    }
}
