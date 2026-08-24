//! M3 "honest capability gap" arms for interpreter extern dispatch.
//!
//! `rt_webgpu_*`, `rt_vk_*`, `rt_gui_*`, `rt_lyon_*`, and `rt_gamepad_*` are
//! declared as `extern fn` throughout `src/lib` and `src/app` (`rt_lyon_*`
//! alone has 49 call sites, `rt_gamepad_*` 20), but unlike `rt_sdl2_*` /
//! `rt_vulkan_*` there is no real native implementation anywhere in this tree
//! to register them against — no C translation unit, no linked Rust runtime
//! crate, nothing a dispatcher could resolve a symbol against. Registering a
//! prefix arm the `sdl2.rs`/`vulkan.rs` way is therefore not possible without
//! fabricating behavior.
//!
//! Left unhandled, every call in these five families falls through to the
//! generic `common::unknown_function` error: `unknown extern function:
//! rt_lyon_fill_tessellate`. That text is indistinguishable from a typo or a
//! genuinely unregistered symbol, and hides the real answer from a caller
//! trying to tell "not built on this host" apart from "does not exist yet
//! anywhere". This module intercepts the five prefixes first and returns a
//! structured capability-gap error instead, naming the family explicitly and
//! pointing at the tracking doc
//! (`doc/04_architecture/runtime/native_library_binding_survey.md` §1).
//!
//! This module does NOT reimplement any of the five families and does NOT
//! return a plausible value for any of them — that would be worse than the
//! generic error, because it would look like success. `rt_vulkan_*` is a
//! different, real family (see `vulkan.rs`) and is deliberately excluded:
//! `rt_vk_*` here is disjoint from `rt_vulkan_*` (the fourth character after
//! `rt_v` differs: `k` vs `u`), and this module must never claim the
//! `rt_vulkan_` prefix.
//!
//! See plan: `doc/03_plan/runtime/native_binding/interpreter_extern_registration_lanes.md`
//! lane R3.

use crate::error::{codes, CompileError, ErrorContext};
use crate::value::Value;

/// Prefixes with no real native implementation anywhere, paired with the
/// short family label used in the capability-gap error message. Order
/// matters only in that longer/more-specific prefixes should precede
/// shorter ones if a future addition could nest; none of the current five
/// do (they are mutually prefix-disjoint from each other and from
/// `rt_vulkan_`).
const CAPABILITY_GAP_FAMILIES: &[(&str, &str)] = &[
    ("rt_webgpu_", "rt_webgpu"),
    ("rt_vk_", "rt_vk"),
    ("rt_gui_", "rt_gui"),
    ("rt_lyon_", "rt_lyon"),
    ("rt_gamepad_", "rt_gamepad"),
];

/// True when `name` falls under one of the M3 capability-gap prefixes.
/// Callers should check this before `dispatch` (mirrors the
/// `name.starts_with(...)` guard shape used for `sdl2`/`vulkan`).
pub fn matches(name: &str) -> bool {
    CAPABILITY_GAP_FAMILIES
        .iter()
        .any(|(prefix, _)| name.starts_with(prefix))
}

/// Return the structured capability-gap error for `name`. `name` must
/// satisfy `matches(name)`; if it does not (should not happen given the
/// `mod.rs` guard), the error still names the full symbol so nothing is
/// silently swallowed.
pub fn dispatch(name: &str) -> Result<Value, CompileError> {
    let family = CAPABILITY_GAP_FAMILIES
        .iter()
        .find(|(prefix, _)| name.starts_with(prefix))
        .map(|(_, fam)| *fam)
        .unwrap_or(name);
    let msg = format!(
        "{family}: no native implementation (capability gap, tracked in \
         native_library_binding_survey.md \u{a7}1): {name}"
    );
    let ctx = ErrorContext::new().with_code(codes::UNDEFINED_FUNCTION).with_help(
        "this family has no native implementation on any target yet; see \
             doc/04_architecture/runtime/native_library_binding_survey.md \u{a7}1 \
             and doc/03_plan/runtime/native_binding/interpreter_extern_registration_lanes.md lane R3",
    );
    Err(CompileError::semantic_with_context(msg, ctx))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn matches_all_five_families() {
        for name in [
            "rt_webgpu_adapter_count",
            "rt_vk_cleanup",
            "rt_gui_get_glyph_8x16",
            "rt_lyon_fill_tessellation_free",
            "rt_gamepad_count",
        ] {
            assert!(matches(name), "expected {name} to match a capability-gap family");
        }
    }

    #[test]
    fn does_not_match_rt_vulkan_or_unrelated_names() {
        for name in ["rt_vulkan_is_available", "rt_sdl2_init", "rt_glfw_init"] {
            assert!(!matches(name), "expected {name} to NOT match a capability-gap family");
        }
    }

    #[test]
    fn dispatch_names_the_family_and_the_full_symbol() {
        let err = dispatch("rt_lyon_fill_tessellate").unwrap_err();
        let text = err.message().to_string();
        assert!(text.contains("rt_lyon"), "message did not name the family: {text}");
        assert!(
            text.contains("rt_lyon_fill_tessellate"),
            "message did not name the full symbol: {text}"
        );
        assert!(
            text.contains("capability gap"),
            "message did not use the capability-gap wording: {text}"
        );
        assert!(
            !text.contains("unknown extern function"),
            "message must not reuse the generic unknown-extern text: {text}"
        );
    }
}
