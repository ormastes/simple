use std::sync::atomic::Ordering;

use crate::error::CompileError;
use crate::value::Value;

use super::{
    get_i64, get_string, get_pixels, int_value, bool_value, tuple_value,
    unsupported_window_mutation, parse_window_config, set_last_error,
    WindowConfig, NEXT_EVENT_LOOP_ID, EVENT_LOOPS, WINDOW_STATES, WINDOW_OWNERS,
    RuntimeCommand,
};
use super::winit_ffi_thread::{start_event_loop_thread, event_to_handle};

#[cfg(target_os = "macos")]
use super::winit_ffi_thread::{macos_pump, MACOS_PUMP};

pub(super) fn dispatch_window(name: &str, args: &[Value]) -> Result<Value, CompileError> {
    match name {
        "rt_winit_event_loop_new" => {
            if !args.is_empty() {
                return Err(super::wrong_arg_count(name, 0, args.len()));
            }
            let id = NEXT_EVENT_LOOP_ID.fetch_add(1, Ordering::SeqCst);
            let handle = start_event_loop_thread(id)?;
            EVENT_LOOPS.lock().insert(id, handle);
            Ok(int_value(id))
        }
        "rt_winit_event_loop_free" => {
            let id = get_i64(args, 0, name)?;
            // Clean up macOS pump state BEFORE removing the event loop handle
            // to avoid "tried to run event handler, but no handler was set" warning
            #[cfg(target_os = "macos")]
            MACOS_PUMP.with(|cell| {
                let mut borrow = cell.borrow_mut();
                if let Some(ps) = borrow.as_ref() {
                    if ps.event_loop_id == id {
                        *borrow = None;
                    }
                }
            });
            if let Some(handle) = EVENT_LOOPS.lock().remove(&id) {
                let _ = handle.command_tx.send(RuntimeCommand::Exit);
            }
            WINDOW_OWNERS.lock().retain(|_, owner| *owner != id);
            WINDOW_STATES.lock().retain(|_, state| state.event_loop_id != id);
            Ok(bool_value(true))
        }
        "rt_winit_event_loop_run_return" => Ok(bool_value(true)),
        "rt_winit_event_loop_poll_events" => {
            let event_loop_id = get_i64(args, 0, name)?;
            let _max_events = get_i64(args, 1, name)?;
            // macOS: pump native events on the main thread
            #[cfg(target_os = "macos")]
            macos_pump(event_loop_id);
            let loops = EVENT_LOOPS.lock();
            if let Some(handle) = loops.get(&event_loop_id) {
                match handle.event_rx.try_recv() {
                    Ok(event) => Ok(int_value(event_to_handle(event))),
                    Err(_) => Ok(int_value(0)),
                }
            } else {
                set_last_error(format!("invalid event loop handle: {event_loop_id}"));
                Ok(int_value(0))
            }
        }
        "rt_winit_event_loop_wait_events" => {
            let event_loop_id = get_i64(args, 0, name)?;
            let timeout_ms = get_i64(args, 1, name)?;
            let loops = EVENT_LOOPS.lock();
            if let Some(handle) = loops.get(&event_loop_id) {
                match handle
                    .event_rx
                    .recv_timeout(std::time::Duration::from_millis(timeout_ms.max(0) as u64))
                {
                    Ok(event) => Ok(int_value(event_to_handle(event))),
                    Err(_) => Ok(int_value(0)),
                }
            } else {
                set_last_error(format!("invalid event loop handle: {event_loop_id}"));
                Ok(int_value(0))
            }
        }
        "rt_winit_window_new" => {
            let event_loop_id = get_i64(args, 0, name)?;
            let mut config = WindowConfig::default();
            config.width = get_i64(args, 1, name)?.max(1) as u32;
            config.height = get_i64(args, 2, name)?.max(1) as u32;
            config.title = get_string(args, 3, name)?;

            let (response_tx, response_rx) = crossbeam::channel::bounded(1);
            {
                let loops = EVENT_LOOPS.lock();
                let Some(handle) = loops.get(&event_loop_id) else {
                    set_last_error(format!("invalid event loop handle: {event_loop_id}"));
                    return Ok(int_value(0));
                };
                handle
                    .command_tx
                    .send(RuntimeCommand::CreateWindow {
                        config,
                        response: response_tx,
                    })
                    .map_err(|err| super::runtime_error(format!("failed to send create window request: {err}")))?;
            } // Release EVENT_LOOPS lock before pumping

            // macOS: pump to process the command on the main thread
            #[cfg(target_os = "macos")]
            for _ in 0..200 {
                macos_pump(event_loop_id);
                if let Ok(result) = response_rx.try_recv() {
                    return match result {
                        Ok(window_id) => Ok(int_value(window_id)),
                        Err(err) => {
                            set_last_error(err);
                            Ok(int_value(0))
                        }
                    };
                }
                std::thread::sleep(std::time::Duration::from_millis(5));
            }

            match response_rx.recv_timeout(std::time::Duration::from_secs(5)) {
                Ok(Ok(window_id)) => Ok(int_value(window_id)),
                Ok(Err(err)) => {
                    set_last_error(err);
                    Ok(int_value(0))
                }
                Err(err) => Err(super::runtime_error(format!(
                    "failed to receive create window response: {err}"
                ))),
            }
        }
        "rt_winit_window_new_with_config" => {
            let event_loop_id = get_i64(args, 0, name)?;
            let config_json = get_string(args, 1, name)?;
            let config = match parse_window_config(&config_json) {
                Ok(config) => config,
                Err(err) => {
                    set_last_error(err);
                    return Ok(int_value(0));
                }
            };
            let loops = EVENT_LOOPS.lock();
            let Some(handle) = loops.get(&event_loop_id) else {
                set_last_error(format!("invalid event loop handle: {event_loop_id}"));
                return Ok(int_value(0));
            };
            let (response_tx, response_rx) = crossbeam::channel::bounded(1);
            handle
                .command_tx
                .send(RuntimeCommand::CreateWindow {
                    config,
                    response: response_tx,
                })
                .map_err(|err| super::runtime_error(format!("failed to send create window request: {err}")))?;
            match response_rx.recv() {
                Ok(Ok(window_id)) => Ok(int_value(window_id)),
                Ok(Err(err)) => {
                    set_last_error(err);
                    Ok(int_value(0))
                }
                Err(err) => Err(super::runtime_error(format!(
                    "failed to receive create window response: {err}"
                ))),
            }
        }
        "rt_winit_window_free" => {
            let window_id = get_i64(args, 0, name)?;
            if let Some(event_loop_id) = WINDOW_OWNERS.lock().get(&window_id).copied() {
                if let Some(handle) = EVENT_LOOPS.lock().get(&event_loop_id) {
                    let _ = handle.command_tx.send(RuntimeCommand::DestroyWindow { window_id });
                    return Ok(bool_value(true));
                }
            }
            set_last_error(format!("invalid window handle: {window_id}"));
            Ok(bool_value(false))
        }
        "rt_winit_window_request_redraw" => {
            let window_id = get_i64(args, 0, name)?;
            if let Some(event_loop_id) = WINDOW_OWNERS.lock().get(&window_id).copied() {
                if let Some(handle) = EVENT_LOOPS.lock().get(&event_loop_id) {
                    let _ = handle.command_tx.send(RuntimeCommand::RequestRedraw { window_id });
                    return Ok(bool_value(true));
                }
            }
            set_last_error(format!("invalid window handle: {window_id}"));
            Ok(bool_value(false))
        }
        "rt_winit_window_present_rgba" => {
            let window_id = get_i64(args, 0, name)?;
            let width = get_i64(args, 1, name)?.max(1) as u32;
            let height = get_i64(args, 2, name)?.max(1) as u32;
            let pixels = get_pixels(args, 3, name)?;
            let event_loop_id = WINDOW_OWNERS.lock().get(&window_id).copied();
            if let Some(el_id) = event_loop_id {
                let (response_tx, response_rx) = crossbeam::channel::bounded(1);
                {
                    if let Some(handle) = EVENT_LOOPS.lock().get(&el_id) {
                        handle
                            .command_tx
                            .send(RuntimeCommand::Present {
                                window_id,
                                width,
                                height,
                                pixels,
                                response: response_tx,
                            })
                            .map_err(|err| super::runtime_error(format!("failed to send present request: {err}")))?;
                    }
                } // Release lock before pumping

                // macOS: pump to process present on main thread
                #[cfg(target_os = "macos")]
                for _ in 0..50 {
                    macos_pump(el_id);
                    if let Ok(result) = response_rx.try_recv() {
                        return match result {
                            Ok(()) => Ok(bool_value(true)),
                            Err(err) => {
                                set_last_error(err);
                                Ok(bool_value(false))
                            }
                        };
                    }
                    std::thread::sleep(std::time::Duration::from_millis(2));
                }

                return match response_rx.recv_timeout(std::time::Duration::from_secs(2)) {
                    Ok(Ok(())) => Ok(bool_value(true)),
                    Ok(Err(err)) => {
                        set_last_error(err);
                        Ok(bool_value(false))
                    }
                    Err(err) => Err(super::runtime_error(format!("failed to receive present response: {err}"))),
                };
            }
            set_last_error(format!("invalid window handle: {window_id}"));
            Ok(bool_value(false))
        }
        "rt_winit_window_get_size" | "rt_winit_window_get_inner_size" | "rt_winit_window_get_outer_size" => {
            let window_id = get_i64(args, 0, name)?;
            let states = WINDOW_STATES.lock();
            if let Some(window) = states.get(&window_id) {
                Ok(tuple_value(vec![
                    Value::Int(window.width as i64),
                    Value::Int(window.height as i64),
                ]))
            } else {
                set_last_error(format!("invalid window handle: {window_id}"));
                Ok(tuple_value(vec![Value::Int(0), Value::Int(0)]))
            }
        }
        "rt_winit_window_get_position" => {
            let window_id = get_i64(args, 0, name)?;
            let states = WINDOW_STATES.lock();
            if let Some(window) = states.get(&window_id) {
                Ok(tuple_value(vec![
                    Value::Int(window.x as i64),
                    Value::Int(window.y as i64),
                ]))
            } else {
                set_last_error(format!("invalid window handle: {window_id}"));
                Ok(tuple_value(vec![Value::Int(0), Value::Int(0)]))
            }
        }
        "rt_winit_window_set_size"
        | "rt_winit_window_set_position"
        | "rt_winit_window_set_min_size"
        | "rt_winit_window_set_max_size"
        | "rt_winit_window_set_title"
        | "rt_winit_window_set_visible"
        | "rt_winit_window_set_resizable"
        | "rt_winit_window_set_minimized"
        | "rt_winit_window_set_maximized"
        | "rt_winit_window_set_fullscreen"
        | "rt_winit_window_set_decorations"
        | "rt_winit_window_set_always_on_top"
        | "rt_winit_window_focus"
        | "rt_winit_window_set_cursor_visible"
        | "rt_winit_window_set_cursor_grab"
        | "rt_winit_window_set_cursor_position" => Ok(unsupported_window_mutation(name)),
        "rt_winit_window_is_visible" => {
            let window_id = get_i64(args, 0, name)?;
            Ok(bool_value(
                WINDOW_STATES.lock().get(&window_id).map(|w| w.visible).unwrap_or(false),
            ))
        }
        "rt_winit_window_is_maximized" => {
            let window_id = get_i64(args, 0, name)?;
            Ok(bool_value(
                WINDOW_STATES
                    .lock()
                    .get(&window_id)
                    .map(|w| w.maximized)
                    .unwrap_or(false),
            ))
        }
        "rt_winit_window_is_fullscreen" => {
            let window_id = get_i64(args, 0, name)?;
            Ok(bool_value(
                WINDOW_STATES
                    .lock()
                    .get(&window_id)
                    .map(|w| w.fullscreen)
                    .unwrap_or(false),
            ))
        }
        "rt_winit_window_id" => {
            let window_id = get_i64(args, 0, name)?;
            Ok(int_value(window_id))
        }
        "rt_winit_window_scale_factor" => {
            let window_id = get_i64(args, 0, name)?;
            Ok(Value::Float(
                WINDOW_STATES
                    .lock()
                    .get(&window_id)
                    .map(|window| window.scale_factor)
                    .unwrap_or(1.0),
            ))
        }
        _ => unreachable!("dispatch_window called with unexpected name: {name}"),
    }
}
