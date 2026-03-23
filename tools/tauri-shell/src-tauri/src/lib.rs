// Mobile entry point — delegates to the shared app module.

mod app;

#[cfg_attr(mobile, tauri::mobile_entry_point)]
pub fn mobile_entry() {
    app::run();
}
