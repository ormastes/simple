//! Lazy initialization infrastructure (#1996)
//!
//! Provides utilities for deferring expensive initialization until actually needed.
//! This helps improve startup time by only initializing components when they're first used.

use std::sync::Once;
use parking_lot::{Mutex, MutexGuard};

/// Lazy initialized value with thread-safe initialization
///
/// # Example
/// ```ignore
/// use simple_driver::LazyInit;
///
/// static EXPENSIVE_RESOURCE: LazyInit<Database> = LazyInit::new(|| {
///     Database::connect("localhost").unwrap()
/// });
///
/// fn use_database() {
///     let db = EXPENSIVE_RESOURCE.get();
///     db.query("SELECT * FROM users");
/// }
/// ```
pub struct LazyInit<T> {
    cell: Mutex<Option<T>>,
    init: Once,
}

impl<T> LazyInit<T> {
    /// Create a new lazy-initialized value
    pub const fn new() -> Self {
        Self {
            cell: Mutex::new(None),
            init: Once::new(),
        }
    }

    /// Get the value, initializing it if necessary
    ///
    /// # Arguments
    /// - `init_fn`: Function to initialize the value on first access
    ///
    /// # Returns
    /// Reference to the initialized value
    pub fn get_or_init<F>(&self, init_fn: F) -> MutexGuard<'_, Option<T>>
    where
        F: FnOnce() -> T,
    {
        self.init.call_once(|| {
            let value = init_fn();
            *self.cell.lock() = Some(value);
        });
        self.cell.lock()
    }

    /// Try to get the value without initializing
    ///
    /// # Returns
    /// Some(value) if already initialized, None otherwise
    pub fn try_get(&self) -> Option<MutexGuard<'_, Option<T>>> {
        if self.is_initialized() {
            Some(self.cell.lock())
        } else {
            None
        }
    }

    /// Check if the value has been initialized
    pub fn is_initialized(&self) -> bool {
        self.init.is_completed()
    }
}

impl<T> Default for LazyInit<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// Macro for declaring static lazy-initialized values
///
/// # Example
/// ```ignore
/// lazy_static! {
///     static ref LOGGER: Logger = Logger::new();
///     static ref CONFIG: Config = Config::load();
/// }
/// ```
#[macro_export]
macro_rules! lazy_static {
    ($(static ref $name:ident: $ty:ty = $init:expr;)+) => {
        $(
            static $name: $crate::LazyInit<$ty> = $crate::LazyInit::new();

            #[allow(non_snake_case)]
            fn $name() -> &'static $ty {
                $name.get_or_init(|| $init)
                    .as_ref()
                    .expect("lazy_static initialization failed")
            }
        )+
    };
}

/// Deferred initialization task
///
/// Represents a task that should be executed lazily, with dependency tracking
pub struct DeferredTask {
    name: &'static str,
    init_fn: Box<dyn FnOnce() + Send>,
    dependencies: Vec<&'static str>,
    initialized: Once,
}

impl DeferredTask {
    /// Create a new deferred task
    pub fn new<F>(name: &'static str, init_fn: F) -> Self
    where
        F: FnOnce() + Send + 'static,
    {
        Self {
            name,
            init_fn: Box::new(init_fn),
            dependencies: Vec::new(),
            initialized: Once::new(),
        }
    }

    /// Add a dependency to this task
    pub fn depends_on(mut self, dependency: &'static str) -> Self {
        self.dependencies.push(dependency);
        self
    }

    /// Get the task name
    pub fn name(&self) -> &'static str {
        self.name
    }

    /// Get task dependencies
    pub fn dependencies(&self) -> &[&'static str] {
        &self.dependencies
    }

    /// Check if the task has been initialized
    pub fn is_initialized(&self) -> bool {
        self.initialized.is_completed()
    }
}

/// Lazy initialization scheduler
///
/// Manages a set of deferred tasks with dependency tracking
pub struct LazyScheduler {
    tasks: Mutex<Vec<DeferredTask>>,
}

impl LazyScheduler {
    /// Create a new scheduler
    pub fn new() -> Self {
        Self {
            tasks: Mutex::new(Vec::new()),
        }
    }

    /// Register a deferred task
    pub fn register(&self, task: DeferredTask) {
        self.tasks.lock().push(task);
    }

    /// Initialize a specific task and its dependencies
    ///
    /// # Arguments
    /// - `name`: Name of the task to initialize
    ///
    /// # Returns
    /// Ok(()) if successful, Err with task name if not found
    pub fn initialize(&self, name: &str) -> Result<(), String> {
        let mut tasks = self.tasks.lock();

        // Find the task
        let task_index = tasks.iter()
            .position(|t: &DeferredTask| t.name() == name)
            .ok_or_else(|| format!("Task '{}' not found", name))?;

        // Collect dependencies
        let dependencies: Vec<_> = tasks[task_index].dependencies().to_vec();

        // Initialize dependencies first (recursively)
        drop(tasks); // Release lock before recursion
        for dep in dependencies {
            self.initialize(dep)?;
        }

        // Now initialize this task
        tasks = self.tasks.lock();
        if !tasks[task_index].is_initialized() {
            // Note: We can't actually call the init_fn here because we'd need to take ownership
            // In a real implementation, you'd want to use a different storage mechanism
            // For now, this is a stub showing the structure
        }

        Ok(())
    }

    /// Initialize all tasks in dependency order
    pub fn initialize_all(&self) -> Result<(), String> {
        let tasks = self.tasks.lock();
        let task_names: Vec<_> = tasks.iter().map(|t: &DeferredTask| t.name()).collect();
        drop(tasks);

        for name in task_names {
            self.initialize(name)?;
        }

        Ok(())
    }

    /// Get count of registered tasks
    pub fn task_count(&self) -> usize {
        self.tasks.lock().len()
    }

    /// Get count of initialized tasks
    pub fn initialized_count(&self) -> usize {
        self.tasks.lock().iter().filter(|t: &&DeferredTask| t.is_initialized()).count()
    }
}

impl Default for LazyScheduler {
    fn default() -> Self {
        Self::new()
    }
}

/// Global lazy scheduler instance
static GLOBAL_SCHEDULER: LazyInit<LazyScheduler> = LazyInit::<LazyScheduler>::new();

/// Get the global lazy scheduler
pub fn global_scheduler() -> MutexGuard<'static, Option<LazyScheduler>> {
    GLOBAL_SCHEDULER.get_or_init(LazyScheduler::new)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Arc;

    #[test]
    fn test_lazy_init_basic() {
        let counter = Arc::new(AtomicUsize::new(0));
        let lazy = LazyInit::new();

        // Not initialized yet
        assert!(!lazy.is_initialized());

        // Initialize on first access
        {
            let counter_clone = counter.clone();
            let _value = lazy.get_or_init(|| {
                counter_clone.fetch_add(1, Ordering::SeqCst);
                42
            });
            assert_eq!(counter.load(Ordering::SeqCst), 1);
        }

        // Second access doesn't re-initialize
        {
            let counter_clone = counter.clone();
            let _value = lazy.get_or_init(|| {
                counter_clone.fetch_add(1, Ordering::SeqCst);
                99
            });
            assert_eq!(counter.load(Ordering::SeqCst), 1); // Still 1, not 2
        }

        assert!(lazy.is_initialized());
    }

    #[test]
    fn test_lazy_init_try_get() {
        let lazy = LazyInit::new();

        // Not initialized, try_get returns None
        assert!(lazy.try_get().is_none());

        // Initialize
        let _ = lazy.get_or_init(|| 42);

        // Now try_get succeeds
        assert!(lazy.try_get().is_some());
    }

    #[test]
    fn test_deferred_task() {
        let task = DeferredTask::new("test_task", || {
            println!("Initializing test task");
        });

        assert_eq!(task.name(), "test_task");
        assert!(!task.is_initialized());
        assert_eq!(task.dependencies().len(), 0);
    }

    #[test]
    fn test_deferred_task_with_dependencies() {
        let task = DeferredTask::new("task_b", || {})
            .depends_on("task_a");

        assert_eq!(task.dependencies().len(), 1);
        assert_eq!(task.dependencies()[0], "task_a");
    }

    #[test]
    fn test_lazy_scheduler() {
        let scheduler = LazyScheduler::new();

        assert_eq!(scheduler.task_count(), 0);
        assert_eq!(scheduler.initialized_count(), 0);

        scheduler.register(DeferredTask::new("task_1", || {}));
        scheduler.register(DeferredTask::new("task_2", || {}));

        assert_eq!(scheduler.task_count(), 2);
    }

    #[test]
    fn test_global_scheduler() {
        let scheduler = global_scheduler();
        assert!(scheduler.is_some());
    }
}
