// Monoio runtime thread with message passing

use super::dispatcher::dispatch_request;
use super::registry::StreamRegistry;
use super::request_builder::build_request_with_response;
use super::types::{IoRequest, IoResponse};
use std::thread;

lazy_static::lazy_static! {
    static ref RUNTIME_THREAD: RuntimeThread = RuntimeThread::new();
}

pub(crate) struct RuntimeThread {
    request_tx: std::sync::mpsc::Sender<IoRequest>,
}

impl RuntimeThread {
    fn new() -> Self {
        let (request_tx, request_rx) = std::sync::mpsc::channel::<IoRequest>();

        // Spawn the runtime thread
        thread::Builder::new()
            .name("monoio-runtime".to_string())
            .spawn(move || {
                Self::runtime_thread_main(request_rx);
            })
            .expect("Failed to spawn monoio runtime thread");

        tracing::info!("Monoio runtime thread started");

        Self { request_tx }
    }

    fn runtime_thread_main(request_rx: std::sync::mpsc::Receiver<IoRequest>) {
        // Create monoio runtime
        let mut rt = monoio::RuntimeBuilder::<monoio::FusionDriver>::new()
            .with_entries(256)
            .build()
            .expect("Failed to create monoio runtime");

        // Run the event loop
        rt.block_on(async move {
            let mut registry = StreamRegistry::new();

            loop {
                // Receive request from FFI
                let request = match request_rx.recv() {
                    Ok(req) => req,
                    Err(_) => {
                        tracing::info!("Request channel closed, shutting down runtime");
                        break;
                    }
                };

                match request {
                    IoRequest::Shutdown => {
                        tracing::info!("Shutdown requested");
                        break;
                    }
                    _ => {
                        dispatch_request(request, &mut registry).await;
                    }
                }
            }

            tracing::info!("Monoio runtime thread exiting");
        });
    }

    /// Send a request and wait for response
    pub fn send_request(&self, request: IoRequest) -> IoResponse {
        let (response_tx, response_rx) = std::sync::mpsc::channel();

        // Add response channel to request
        let request_with_tx = build_request_with_response(request, response_tx);

        // Send request to runtime thread
        if let Err(e) = self.request_tx.send(request_with_tx) {
            return IoResponse::Error {
                code: -1,
                message: format!("Failed to send request: {}", e),
            };
        }

        // Wait for response
        match response_rx.recv() {
            Ok(response) => response,
            Err(e) => IoResponse::Error {
                code: -1,
                message: format!("Failed to receive response: {}", e),
            },
        }
    }
}

/// Initialize the runtime thread (called once)
pub fn init_runtime_thread() {
    // Access the lazy_static to ensure thread is started
    let _ = &*RUNTIME_THREAD;
}

/// Send a request to the runtime thread and wait for response
pub fn send_request(request: IoRequest) -> IoResponse {
    RUNTIME_THREAD.send_request(request)
}
