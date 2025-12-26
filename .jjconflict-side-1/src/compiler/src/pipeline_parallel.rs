//! Pipeline Parallelism (#812)
//!
//! Enables concurrent execution of different compilation stages for different modules.
//! While module A is in codegen, module B can be in MIR lowering, module C in HIR lowering, etc.
//!
//! # Pipeline Stages
//!
//! ```text
//! Parse → HIR → Monomorphize → MIR → Codegen → Link
//!   ↓       ↓        ↓          ↓       ↓        ↓
//!  S1      S2       S3         S4      S5       S6
//! ```
//!
//! # Example
//!
//! With 3 modules and 4 threads:
//! ```text
//! Time →
//! T1: [Parse A] [HIR A] [Mono A] [MIR A] [Codegen A]
//! T2:           [Parse B] [HIR B] [Mono B] [MIR B] [Codegen B]
//! T3:                     [Parse C] [HIR C] [Mono C] [MIR C] [Codegen C]
//! T4:                               [Link all when ready]
//! ```

use parking_lot::RwLock;
use rayon::prelude::*;
use std::collections::HashMap;
use std::sync::mpsc::{channel, Receiver, Sender, TryRecvError};
use std::sync::Arc;

/// Compilation stage in the pipeline.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PipelineStage {
    /// Parsing source to AST
    Parse,
    /// Lowering AST to HIR
    HirLower,
    /// Monomorphizing generics
    Monomorphize,
    /// Lowering HIR to MIR
    MirLower,
    /// Generating code
    Codegen,
    /// Linking modules
    Link,
}

impl PipelineStage {
    /// Get the next stage in the pipeline.
    pub fn next(&self) -> Option<PipelineStage> {
        match self {
            PipelineStage::Parse => Some(PipelineStage::HirLower),
            PipelineStage::HirLower => Some(PipelineStage::Monomorphize),
            PipelineStage::Monomorphize => Some(PipelineStage::MirLower),
            PipelineStage::MirLower => Some(PipelineStage::Codegen),
            PipelineStage::Codegen => Some(PipelineStage::Link),
            PipelineStage::Link => None,
        }
    }

    /// Get all stages in order.
    pub fn all() -> &'static [PipelineStage] {
        &[
            PipelineStage::Parse,
            PipelineStage::HirLower,
            PipelineStage::Monomorphize,
            PipelineStage::MirLower,
            PipelineStage::Codegen,
            PipelineStage::Link,
        ]
    }

    /// Get the stage name.
    pub fn name(&self) -> &'static str {
        match self {
            PipelineStage::Parse => "Parse",
            PipelineStage::HirLower => "HIR",
            PipelineStage::Monomorphize => "Mono",
            PipelineStage::MirLower => "MIR",
            PipelineStage::Codegen => "Codegen",
            PipelineStage::Link => "Link",
        }
    }
}

/// Work item in the pipeline.
#[derive(Debug)]
pub struct PipelineWork<T> {
    /// Module identifier.
    pub module_id: usize,
    /// Module name.
    pub module_name: String,
    /// Current stage.
    pub stage: PipelineStage,
    /// Data for processing.
    pub data: T,
}

/// Configuration for pipeline parallelism.
#[derive(Debug, Clone)]
pub struct PipelineConfig {
    /// Maximum number of modules in flight.
    pub max_in_flight: usize,
    /// Channel buffer size per stage.
    pub channel_buffer: usize,
    /// Whether to enable stage profiling.
    pub profile: bool,
}

impl Default for PipelineConfig {
    fn default() -> Self {
        Self {
            max_in_flight: 8,
            channel_buffer: 16,
            profile: false,
        }
    }
}

impl PipelineConfig {
    /// Create a new config.
    pub fn new() -> Self {
        Self::default()
    }

    /// Set maximum modules in flight.
    pub fn with_max_in_flight(mut self, n: usize) -> Self {
        self.max_in_flight = n;
        self
    }

    /// Set channel buffer size.
    pub fn with_buffer(mut self, n: usize) -> Self {
        self.channel_buffer = n;
        self
    }

    /// Enable profiling.
    pub fn with_profiling(mut self, enabled: bool) -> Self {
        self.profile = enabled;
        self
    }
}

/// Statistics about pipeline execution.
#[derive(Debug, Clone, Default)]
pub struct PipelineStats {
    /// Number of modules processed per stage.
    pub modules_per_stage: HashMap<PipelineStage, usize>,
    /// Total modules processed.
    pub total_modules: usize,
    /// Number of pipeline stalls (waiting for work).
    pub stalls: usize,
    /// Maximum concurrent modules in flight.
    pub max_concurrent: usize,
}

impl PipelineStats {
    /// Record a module completing a stage.
    pub fn record_stage(&mut self, stage: PipelineStage) {
        *self.modules_per_stage.entry(stage).or_insert(0) += 1;
    }

    /// Record pipeline stall.
    pub fn record_stall(&mut self) {
        self.stalls += 1;
    }

    /// Update max concurrent modules.
    pub fn update_concurrent(&mut self, current: usize) {
        if current > self.max_concurrent {
            self.max_concurrent = current;
        }
    }
}

/// Pipeline stage handler trait.
/// Implement this for each stage of the compilation pipeline.
pub trait StageHandler<In, Out>: Send + Sync {
    /// Process work from the input type to the output type.
    fn process(&self, input: In, module_id: usize, module_name: &str) -> Result<Out, String>;

    /// Get the stage this handler is for.
    fn stage(&self) -> PipelineStage;
}

/// A simple in-memory work queue for pipeline stages.
pub struct PipelineQueue<T> {
    sender: Sender<T>,
    receiver: std::sync::Mutex<Receiver<T>>,
    count: std::sync::atomic::AtomicUsize,
}

impl<T> PipelineQueue<T> {
    /// Create a new queue.
    pub fn new() -> Self {
        let (sender, receiver) = channel();
        Self {
            sender,
            receiver: std::sync::Mutex::new(receiver),
            count: std::sync::atomic::AtomicUsize::new(0),
        }
    }

    /// Send work to the queue.
    pub fn send(&self, work: T) -> Result<(), std::sync::mpsc::SendError<T>> {
        self.count.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        self.sender.send(work)
    }

    /// Receive work from the queue (blocking).
    pub fn recv(&self) -> Result<T, std::sync::mpsc::RecvError> {
        let receiver = self.receiver.lock().unwrap();
        let result = receiver.recv();
        if result.is_ok() {
            self.count.fetch_sub(1, std::sync::atomic::Ordering::SeqCst);
        }
        result
    }

    /// Try to receive work (non-blocking).
    pub fn try_recv(&self) -> Option<T> {
        let receiver = self.receiver.lock().unwrap();
        match receiver.try_recv() {
            Ok(item) => {
                self.count.fetch_sub(1, std::sync::atomic::Ordering::SeqCst);
                Some(item)
            }
            Err(_) => None,
        }
    }

    /// Check if the queue is empty.
    pub fn is_empty(&self) -> bool {
        self.count.load(std::sync::atomic::Ordering::SeqCst) == 0
    }

    /// Get the number of items in the queue.
    pub fn len(&self) -> usize {
        self.count.load(std::sync::atomic::Ordering::SeqCst)
    }

    /// Clone the sender for use by multiple producers.
    pub fn sender(&self) -> Sender<T> {
        self.sender.clone()
    }
}

impl<T> Default for PipelineQueue<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// Pipeline coordinator that manages stage execution.
pub struct PipelineCoordinator {
    config: PipelineConfig,
    stats: RwLock<PipelineStats>,
    in_flight: RwLock<usize>,
}

impl PipelineCoordinator {
    /// Create a new pipeline coordinator.
    pub fn new() -> Self {
        Self::with_config(PipelineConfig::default())
    }

    /// Create with custom config.
    pub fn with_config(config: PipelineConfig) -> Self {
        Self {
            config,
            stats: RwLock::new(PipelineStats::default()),
            in_flight: RwLock::new(0),
        }
    }

    /// Get current statistics.
    pub fn stats(&self) -> PipelineStats {
        self.stats.read().clone()
    }

    /// Reset statistics.
    pub fn reset_stats(&self) {
        *self.stats.write() = PipelineStats::default();
    }

    /// Check if we can start a new module.
    pub fn can_start_module(&self) -> bool {
        *self.in_flight.read() < self.config.max_in_flight
    }

    /// Mark a module as started.
    pub fn start_module(&self) {
        let mut count = self.in_flight.write();
        *count += 1;
        self.stats.write().update_concurrent(*count);
    }

    /// Mark a module as completed.
    pub fn complete_module(&self) {
        let mut count = self.in_flight.write();
        *count = count.saturating_sub(1);
        self.stats.write().total_modules += 1;
    }

    /// Record stage completion.
    pub fn record_stage(&self, stage: PipelineStage) {
        self.stats.write().record_stage(stage);
    }

    /// Record a stall.
    pub fn record_stall(&self) {
        self.stats.write().record_stall();
    }

    /// Get config.
    pub fn config(&self) -> &PipelineConfig {
        &self.config
    }
}

impl Default for PipelineCoordinator {
    fn default() -> Self {
        Self::new()
    }
}

/// Simple parallel pipeline executor.
/// Processes items through all stages using rayon's parallel iterators.
///
/// Type parameters:
/// - S1..S5: Stage handlers for Parse, HIR, Mono, MIR, Codegen
/// - A..E: Intermediate types between stages
pub struct ParallelPipeline<S1, S2, S3, S4, S5, A, B, C, D, E>
where
    S1: StageHandler<String, A>,
    S2: StageHandler<A, B>,
    S3: StageHandler<B, C>,
    S4: StageHandler<C, D>,
    S5: StageHandler<D, E>,
{
    parse: Arc<S1>,
    hir: Arc<S2>,
    mono: Arc<S3>,
    mir: Arc<S4>,
    codegen: Arc<S5>,
    coordinator: Arc<PipelineCoordinator>,
    _phantom: std::marker::PhantomData<(A, B, C, D, E)>,
}

impl<S1, S2, S3, S4, S5, A, B, C, D, E> ParallelPipeline<S1, S2, S3, S4, S5, A, B, C, D, E>
where
    S1: StageHandler<String, A> + 'static,
    S2: StageHandler<A, B> + 'static,
    S3: StageHandler<B, C> + 'static,
    S4: StageHandler<C, D> + 'static,
    S5: StageHandler<D, E> + 'static,
    A: Send + Sync + 'static,
    B: Send + Sync + 'static,
    C: Send + Sync + 'static,
    D: Send + Sync + 'static,
    E: Send + Sync + 'static,
{
    /// Create a new parallel pipeline.
    pub fn new(parse: S1, hir: S2, mono: S3, mir: S4, codegen: S5) -> Self {
        Self {
            parse: Arc::new(parse),
            hir: Arc::new(hir),
            mono: Arc::new(mono),
            mir: Arc::new(mir),
            codegen: Arc::new(codegen),
            coordinator: Arc::new(PipelineCoordinator::new()),
            _phantom: std::marker::PhantomData,
        }
    }

    /// Create with custom coordinator.
    pub fn with_coordinator(
        parse: S1,
        hir: S2,
        mono: S3,
        mir: S4,
        codegen: S5,
        coordinator: PipelineCoordinator,
    ) -> Self {
        Self {
            parse: Arc::new(parse),
            hir: Arc::new(hir),
            mono: Arc::new(mono),
            mir: Arc::new(mir),
            codegen: Arc::new(codegen),
            coordinator: Arc::new(coordinator),
            _phantom: std::marker::PhantomData,
        }
    }

    /// Process multiple sources through the pipeline.
    pub fn process(&self, sources: Vec<(String, String)>) -> Vec<Result<E, String>> {
        sources
            .into_par_iter()
            .enumerate()
            .map(|(id, (name, source))| {
                self.coordinator.start_module();

                // Parse
                let parsed = self.parse.process(source, id, &name)?;
                self.coordinator.record_stage(PipelineStage::Parse);

                // HIR
                let hir = self.hir.process(parsed, id, &name)?;
                self.coordinator.record_stage(PipelineStage::HirLower);

                // Monomorphize
                let mono = self.mono.process(hir, id, &name)?;
                self.coordinator.record_stage(PipelineStage::Monomorphize);

                // MIR
                let mir = self.mir.process(mono, id, &name)?;
                self.coordinator.record_stage(PipelineStage::MirLower);

                // Codegen
                let result = self.codegen.process(mir, id, &name)?;
                self.coordinator.record_stage(PipelineStage::Codegen);

                self.coordinator.complete_module();
                Ok(result)
            })
            .collect()
    }

    /// Get pipeline statistics.
    pub fn stats(&self) -> PipelineStats {
        self.coordinator.stats()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pipeline_stage_order() {
        let stages = PipelineStage::all();
        assert_eq!(stages.len(), 6);
        assert_eq!(stages[0], PipelineStage::Parse);
        assert_eq!(stages[5], PipelineStage::Link);
    }

    #[test]
    fn test_pipeline_stage_next() {
        assert_eq!(PipelineStage::Parse.next(), Some(PipelineStage::HirLower));
        assert_eq!(PipelineStage::Codegen.next(), Some(PipelineStage::Link));
        assert_eq!(PipelineStage::Link.next(), None);
    }

    #[test]
    fn test_pipeline_config() {
        let config = PipelineConfig::new()
            .with_max_in_flight(16)
            .with_buffer(32)
            .with_profiling(true);

        assert_eq!(config.max_in_flight, 16);
        assert_eq!(config.channel_buffer, 32);
        assert!(config.profile);
    }

    #[test]
    fn test_pipeline_stats() {
        let mut stats = PipelineStats::default();

        stats.record_stage(PipelineStage::Parse);
        stats.record_stage(PipelineStage::Parse);
        stats.record_stage(PipelineStage::HirLower);

        assert_eq!(*stats.modules_per_stage.get(&PipelineStage::Parse).unwrap(), 2);
        assert_eq!(*stats.modules_per_stage.get(&PipelineStage::HirLower).unwrap(), 1);
    }

    #[test]
    fn test_pipeline_queue() {
        let queue: PipelineQueue<i32> = PipelineQueue::new();

        queue.send(1).unwrap();
        queue.send(2).unwrap();
        queue.send(3).unwrap();

        assert_eq!(queue.len(), 3);
        assert_eq!(queue.recv().unwrap(), 1);
        assert_eq!(queue.recv().unwrap(), 2);
        assert_eq!(queue.len(), 1);
    }

    #[test]
    fn test_pipeline_coordinator() {
        let coord = PipelineCoordinator::with_config(
            PipelineConfig::new().with_max_in_flight(2)
        );

        assert!(coord.can_start_module());
        coord.start_module();
        assert!(coord.can_start_module());
        coord.start_module();
        assert!(!coord.can_start_module());

        coord.complete_module();
        assert!(coord.can_start_module());

        let stats = coord.stats();
        assert_eq!(stats.max_concurrent, 2);
        assert_eq!(stats.total_modules, 1);
    }

    // Test handlers for pipeline
    struct MockParseHandler;
    impl StageHandler<String, i32> for MockParseHandler {
        fn process(&self, input: String, _id: usize, _name: &str) -> Result<i32, String> {
            Ok(input.len() as i32)
        }
        fn stage(&self) -> PipelineStage { PipelineStage::Parse }
    }

    struct MockHirHandler;
    impl StageHandler<i32, i32> for MockHirHandler {
        fn process(&self, input: i32, _id: usize, _name: &str) -> Result<i32, String> {
            Ok(input * 2)
        }
        fn stage(&self) -> PipelineStage { PipelineStage::HirLower }
    }

    struct MockMonoHandler;
    impl StageHandler<i32, i32> for MockMonoHandler {
        fn process(&self, input: i32, _id: usize, _name: &str) -> Result<i32, String> {
            Ok(input + 1)
        }
        fn stage(&self) -> PipelineStage { PipelineStage::Monomorphize }
    }

    struct MockMirHandler;
    impl StageHandler<i32, i32> for MockMirHandler {
        fn process(&self, input: i32, _id: usize, _name: &str) -> Result<i32, String> {
            Ok(input * 3)
        }
        fn stage(&self) -> PipelineStage { PipelineStage::MirLower }
    }

    struct MockCodegenHandler;
    impl StageHandler<i32, String> for MockCodegenHandler {
        fn process(&self, input: i32, _id: usize, name: &str) -> Result<String, String> {
            Ok(format!("{}: {}", name, input))
        }
        fn stage(&self) -> PipelineStage { PipelineStage::Codegen }
    }

    #[test]
    fn test_parallel_pipeline() {
        let pipeline = ParallelPipeline::new(
            MockParseHandler,
            MockHirHandler,
            MockMonoHandler,
            MockMirHandler,
            MockCodegenHandler,
        );

        let sources = vec![
            ("mod1".to_string(), "hello".to_string()),
            ("mod2".to_string(), "world!".to_string()),
        ];

        let results = pipeline.process(sources);

        assert_eq!(results.len(), 2);
        // "hello" = 5 chars, *2 = 10, +1 = 11, *3 = 33
        assert_eq!(results[0].as_ref().unwrap(), "mod1: 33");
        // "world!" = 6 chars, *2 = 12, +1 = 13, *3 = 39
        assert_eq!(results[1].as_ref().unwrap(), "mod2: 39");

        let stats = pipeline.stats();
        assert_eq!(stats.total_modules, 2);
    }
}
