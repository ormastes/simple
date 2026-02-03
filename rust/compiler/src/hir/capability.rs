//! Capability checking infrastructure for reference capabilities
//!
//! This module implements compile-time capability checking to enforce:
//! - Aliasing rules (no mutable aliasing)
//! - Capability conversion rules (downgrade only)
//! - Thread safety (iso T transferable across threads)

use super::types::ConcurrencyMode;
use simple_parser::ast::ReferenceCapability;
use std::collections::HashMap;

/// Environment tracking active capabilities for aliasing analysis
#[derive(Debug, Clone, Default)]
pub struct CapabilityEnv {
    /// Maps variable/reference ID to its current capability
    active: HashMap<usize, ReferenceCapability>,
}

impl CapabilityEnv {
    /// Create a new empty capability environment
    pub fn new() -> Self {
        Self { active: HashMap::new() }
    }

    /// Check if a capability can be acquired without aliasing violations
    pub fn can_acquire(&self, id: usize, cap: ReferenceCapability) -> Result<(), CapabilityError> {
        // Check if this ID already has an active capability
        if let Some(existing) = self.active.get(&id) {
            // If there's an active exclusive or isolated capability, no aliasing is allowed
            return Err(CapabilityError::AliasingViolation {
                id,
                existing: *existing,
                requested: cap,
            });
        }

        // If no existing capability, or existing is shared (not tracked), acquisition is allowed
        Ok(())
    }

    /// Acquire a capability for a reference
    pub fn acquire(&mut self, id: usize, cap: ReferenceCapability) {
        if !cap.is_shared() {
            self.active.insert(id, cap);
        }
    }

    /// Release a capability (e.g., when a reference goes out of scope)
    pub fn release(&mut self, id: usize) {
        self.active.remove(&id);
    }

    /// Check if a capability conversion is valid
    pub fn can_convert(from: ReferenceCapability, to: ReferenceCapability) -> Result<(), CapabilityError> {
        match (from, to) {
            // Identity conversions are always valid
            (a, b) if a == b => Ok(()),

            // Downgrade: mut T → T (exclusive to shared)
            (ReferenceCapability::Exclusive, ReferenceCapability::Shared) => Ok(()),

            // Downgrade: iso T → mut T (isolated to exclusive)
            (ReferenceCapability::Isolated, ReferenceCapability::Exclusive) => Ok(()),

            // Downgrade: iso T → T (isolated to shared)
            (ReferenceCapability::Isolated, ReferenceCapability::Shared) => Ok(()),

            // All other conversions are invalid (upcasts)
            _ => Err(CapabilityError::InvalidConversion { from, to }),
        }
    }

    /// Check if a capability allows mutation
    pub fn allows_mutation(cap: ReferenceCapability) -> bool {
        cap.allows_mutation()
    }

    /// Check if a capability can be transferred across threads/actors
    pub fn is_transferable(cap: ReferenceCapability) -> bool {
        cap.is_transferable()
    }

    /// Check if a capability is compatible with a concurrency mode
    pub fn check_mode_compatibility(
        cap: ReferenceCapability,
        mode: ConcurrencyMode,
        context: &str,
    ) -> Result<(), CapabilityError> {
        match cap {
            ReferenceCapability::Exclusive if !mode.allows_mut() => Err(CapabilityError::MutInActorMode {
                function: context.to_string(),
            }),
            _ => Ok(()),
        }
    }
}

/// Errors that can occur during capability checking
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CapabilityError {
    /// Aliasing violation: tried to acquire exclusive/isolated capability while another exists
    AliasingViolation {
        id: usize,
        existing: ReferenceCapability,
        requested: ReferenceCapability,
    },

    /// Invalid capability conversion (upcast)
    InvalidConversion {
        from: ReferenceCapability,
        to: ReferenceCapability,
    },

    /// Tried to use mut T in actor mode (only allowed in lock_base/unsafe)
    MutInActorMode { function: String },

    /// Mutation not allowed on this capability
    MutationNotAllowed { capability: ReferenceCapability },
}

impl std::fmt::Display for CapabilityError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CapabilityError::AliasingViolation {
                id,
                existing,
                requested,
            } => {
                writeln!(
                    f,
                    "Aliasing violation: reference {} already has {:?} capability, cannot acquire {:?}",
                    id, existing, requested
                )?;
                writeln!(
                    f,
                    "\nHint: Exclusive and isolated capabilities cannot coexist with any other reference."
                )?;
                write!(f, "      Only shared (T) references can be aliased.")
            }
            CapabilityError::InvalidConversion { from, to } => {
                writeln!(
                    f,
                    "Invalid capability conversion: cannot convert {:?} to {:?}",
                    from, to
                )?;
                writeln!(f, "\nHint: Capabilities can only be downgraded, not upgraded:")?;
                writeln!(f, "      ✓ iso T → mut T  (consume to mutable)")?;
                writeln!(f, "      ✓ iso T → T      (consume to shared)")?;
                writeln!(f, "      ✓ mut T → T      (downgrade to shared)")?;
                write!(f, "      ✗ T → mut T      (cannot upgrade)")
            }
            CapabilityError::MutInActorMode { function } => {
                writeln!(f, "Cannot use 'mut T' in actor mode (function: {})", function)?;
                writeln!(
                    f,
                    "\nActor mode enforces message-passing concurrency with no shared mutable state."
                )?;
                writeln!(f, "\nTo fix this, choose one of:")?;
                writeln!(f, "  1. Use iso T for transferable unique references:")?;
                writeln!(f, "     fn {}(x: iso Data) -> ...", function)?;
                writeln!(f, "\n  2. Switch to lock_base mode for shared mutable state:")?;
                write!(
                    f,
                    "     #[concurrency_mode(lock_base)]\n     fn {}(x: mut Data) -> ...",
                    function
                )
            }
            CapabilityError::MutationNotAllowed { capability } => {
                writeln!(f, "Mutation not allowed on {:?} capability", capability)?;
                writeln!(f, "\nHint: Only mut T and iso T allow mutation.")?;
                write!(f, "      Shared references (T) are read-only.")
            }
        }
    }
}

impl std::error::Error for CapabilityError {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_shared_always_acquirable() {
        let env = CapabilityEnv::new();
        assert!(env.can_acquire(1, ReferenceCapability::Shared).is_ok());
        assert!(env.can_acquire(1, ReferenceCapability::Shared).is_ok());
    }

    #[test]
    fn test_exclusive_no_aliasing() {
        let mut env = CapabilityEnv::new();
        env.acquire(1, ReferenceCapability::Exclusive);
        assert!(env.can_acquire(1, ReferenceCapability::Exclusive).is_err());
        assert!(env.can_acquire(1, ReferenceCapability::Shared).is_err());
    }

    #[test]
    fn test_isolated_no_aliasing() {
        let mut env = CapabilityEnv::new();
        env.acquire(1, ReferenceCapability::Isolated);
        assert!(env.can_acquire(1, ReferenceCapability::Isolated).is_err());
        assert!(env.can_acquire(1, ReferenceCapability::Exclusive).is_err());
    }

    #[test]
    fn test_release_allows_reacquire() {
        let mut env = CapabilityEnv::new();
        env.acquire(1, ReferenceCapability::Exclusive);
        assert!(env.can_acquire(1, ReferenceCapability::Exclusive).is_err());
        env.release(1);
        assert!(env.can_acquire(1, ReferenceCapability::Exclusive).is_ok());
    }

    #[test]
    fn test_valid_conversions() {
        // mut T → T (downgrade)
        assert!(CapabilityEnv::can_convert(ReferenceCapability::Exclusive, ReferenceCapability::Shared).is_ok());

        // iso T → mut T (consume)
        assert!(CapabilityEnv::can_convert(ReferenceCapability::Isolated, ReferenceCapability::Exclusive).is_ok());

        // iso T → T (consume)
        assert!(CapabilityEnv::can_convert(ReferenceCapability::Isolated, ReferenceCapability::Shared).is_ok());
    }

    #[test]
    fn test_invalid_conversions() {
        // T → mut T (upcast, invalid)
        assert!(CapabilityEnv::can_convert(ReferenceCapability::Shared, ReferenceCapability::Exclusive).is_err());

        // T → iso T (upcast, invalid)
        assert!(CapabilityEnv::can_convert(ReferenceCapability::Shared, ReferenceCapability::Isolated).is_err());

        // mut T → iso T (upcast, invalid)
        assert!(CapabilityEnv::can_convert(ReferenceCapability::Exclusive, ReferenceCapability::Isolated).is_err());
    }

    #[test]
    fn test_mode_allows_mut() {
        // Actor mode forbids mut T
        assert!(!ConcurrencyMode::Actor.allows_mut());

        // LockBase mode allows mut T
        assert!(ConcurrencyMode::LockBase.allows_mut());

        // Unsafe mode allows mut T
        assert!(ConcurrencyMode::Unsafe.allows_mut());
    }

    #[test]
    fn test_mode_allows_iso() {
        // iso T allowed in all modes (for message passing)
        assert!(ConcurrencyMode::Actor.allows_iso());
        assert!(ConcurrencyMode::LockBase.allows_iso());
        assert!(ConcurrencyMode::Unsafe.allows_iso());
    }

    #[test]
    fn test_mode_compatibility_actor() {
        // Actor mode: mut T forbidden
        assert!(CapabilityEnv::check_mode_compatibility(
            ReferenceCapability::Exclusive,
            ConcurrencyMode::Actor,
            "test_fn"
        )
        .is_err());

        // Actor mode: iso T allowed
        assert!(CapabilityEnv::check_mode_compatibility(
            ReferenceCapability::Isolated,
            ConcurrencyMode::Actor,
            "test_fn"
        )
        .is_ok());

        // Actor mode: shared allowed
        assert!(CapabilityEnv::check_mode_compatibility(
            ReferenceCapability::Shared,
            ConcurrencyMode::Actor,
            "test_fn"
        )
        .is_ok());
    }

    #[test]
    fn test_mode_compatibility_lock_base() {
        // LockBase mode: all capabilities allowed
        assert!(CapabilityEnv::check_mode_compatibility(
            ReferenceCapability::Exclusive,
            ConcurrencyMode::LockBase,
            "test_fn"
        )
        .is_ok());

        assert!(CapabilityEnv::check_mode_compatibility(
            ReferenceCapability::Isolated,
            ConcurrencyMode::LockBase,
            "test_fn"
        )
        .is_ok());

        assert!(CapabilityEnv::check_mode_compatibility(
            ReferenceCapability::Shared,
            ConcurrencyMode::LockBase,
            "test_fn"
        )
        .is_ok());
    }

    #[test]
    fn test_mode_compatibility_unsafe() {
        // Unsafe mode: all capabilities allowed
        assert!(CapabilityEnv::check_mode_compatibility(
            ReferenceCapability::Exclusive,
            ConcurrencyMode::Unsafe,
            "test_fn"
        )
        .is_ok());

        assert!(CapabilityEnv::check_mode_compatibility(
            ReferenceCapability::Isolated,
            ConcurrencyMode::Unsafe,
            "test_fn"
        )
        .is_ok());

        assert!(CapabilityEnv::check_mode_compatibility(
            ReferenceCapability::Shared,
            ConcurrencyMode::Unsafe,
            "test_fn"
        )
        .is_ok());
    }

    #[test]
    fn test_mode_from_attr() {
        assert_eq!(ConcurrencyMode::from_attr_arg("actor"), Some(ConcurrencyMode::Actor));
        assert_eq!(
            ConcurrencyMode::from_attr_arg("lock_base"),
            Some(ConcurrencyMode::LockBase)
        );
        assert_eq!(ConcurrencyMode::from_attr_arg("unsafe"), Some(ConcurrencyMode::Unsafe));
        assert_eq!(ConcurrencyMode::from_attr_arg("invalid"), None);
    }
}
