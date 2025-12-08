use tracing_subscriber::{fmt, layer::SubscriberExt, util::SubscriberInitExt, EnvFilter};

/// Initialize structured logging with env-based filtering.
///
/// - Controlled by `RUST_LOG`/`SIMPLE_LOG` env vars (e.g., `SIMPLE_LOG=info`).
/// - Uses span-based, structured logging via `tracing`.
pub fn init() {
    let env_filter = EnvFilter::try_from_env("SIMPLE_LOG")
        .or_else(|_| EnvFilter::try_from_env("RUST_LOG"))
        .unwrap_or_else(|_| EnvFilter::new("info"));

    let fmt_layer = fmt::layer().with_target(true).with_line_number(true);
    tracing_subscriber::registry().with(env_filter).with(fmt_layer).init();
}
