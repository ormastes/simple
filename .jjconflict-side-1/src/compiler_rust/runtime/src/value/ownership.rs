//! Runtime ownership-region state machine for safe transfer envelopes.
//!
//! This module tracks authority only. It does not make an arbitrary
//! `RuntimeValue` graph isolated, and it intentionally stores no raw heap
//! pointer as transport payload.

use std::collections::HashMap;

use super::transfer::{RuntimeTransferEnvelopeV1, TransferDomain, TransferMode, TransferPayload};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RuntimeOwnershipState {
    Local {
        owner: TransferDomain,
        generation: u64,
    },
    InTransit {
        source: TransferDomain,
        destination: TransferDomain,
        generation: u64,
        token: u64,
    },
    FrozenShared {
        generation: u64,
    },
}

#[derive(Default)]
pub(crate) struct RuntimeOwnershipRegistry {
    next_region: u64,
    next_token: u64,
    states: HashMap<u64, RuntimeOwnershipState>,
}

impl RuntimeOwnershipRegistry {
    pub(crate) fn new() -> Self {
        Self {
            next_region: 1,
            next_token: 1,
            states: HashMap::new(),
        }
    }

    /// Register authority for a region that a future graph sealer has already
    /// proven disconnected. This API records no payload and is not itself
    /// evidence that an arbitrary RuntimeValue graph is isolated.
    pub(crate) fn register_sealed_region(&mut self, owner: TransferDomain) -> Option<u64> {
        let region = self.next_region;
        self.next_region = self.next_region.checked_add(1)?;
        self.states
            .insert(region, RuntimeOwnershipState::Local { owner, generation: 0 });
        Some(region)
    }

    pub(crate) fn state(&self, region: u64) -> Option<RuntimeOwnershipState> {
        self.states.get(&region).copied()
    }

    pub(crate) fn begin_move(
        &mut self,
        region: u64,
        source: TransferDomain,
        destination: TransferDomain,
    ) -> Option<RuntimeTransferEnvelopeV1> {
        let RuntimeOwnershipState::Local { owner, generation } = self.state(region)? else {
            return None;
        };
        if owner != source || source == destination {
            return None;
        }
        let token = self.next_token;
        self.next_token = self.next_token.checked_add(1)?;
        let envelope = RuntimeTransferEnvelopeV1 {
            region_id: region,
            generation,
            source_domain: source,
            target_domain: destination,
            mode: TransferMode::OwnedMove,
            payload: TransferPayload::OwnedRegion,
            ownership_token: token,
            source_invalidated: true,
        };
        if !envelope.boundary_allowed() {
            return None;
        }
        self.states.insert(
            region,
            RuntimeOwnershipState::InTransit {
                source,
                destination,
                generation,
                token,
            },
        );
        Some(envelope)
    }

    pub(crate) fn receive_move(&mut self, envelope: RuntimeTransferEnvelopeV1, receiver: TransferDomain) -> bool {
        let Some(RuntimeOwnershipState::InTransit {
            source,
            destination,
            generation,
            token,
        }) = self.state(envelope.region_id)
        else {
            return false;
        };
        if receiver != destination
            || envelope.source_domain != source
            || envelope.target_domain != destination
            || envelope.generation != generation
            || envelope.ownership_token != token
            || !envelope.boundary_allowed()
        {
            return false;
        }
        let Some(next_generation) = generation.checked_add(1) else {
            return false;
        };
        self.states.insert(
            envelope.region_id,
            RuntimeOwnershipState::Local {
                owner: receiver,
                generation: next_generation,
            },
        );
        true
    }

    pub(crate) fn rollback_move(&mut self, envelope: RuntimeTransferEnvelopeV1) -> bool {
        let Some(RuntimeOwnershipState::InTransit {
            source,
            destination,
            generation,
            token,
        }) = self.state(envelope.region_id)
        else {
            return false;
        };
        if envelope.source_domain != source
            || envelope.target_domain != destination
            || envelope.generation != generation
            || envelope.ownership_token != token
        {
            return false;
        }
        let Some(next_generation) = generation.checked_add(1) else {
            return false;
        };
        self.states.insert(
            envelope.region_id,
            RuntimeOwnershipState::Local {
                owner: source,
                generation: next_generation,
            },
        );
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn move_invalidates_source_until_exact_receipt() {
        let mut registry = RuntimeOwnershipRegistry::new();
        let region = registry.register_sealed_region(TransferDomain::Parent).unwrap();
        let envelope = registry
            .begin_move(region, TransferDomain::Parent, TransferDomain::Thread)
            .unwrap();
        assert!(matches!(
            registry.state(region),
            Some(RuntimeOwnershipState::InTransit { .. })
        ));
        assert!(registry
            .begin_move(region, TransferDomain::Parent, TransferDomain::Actor)
            .is_none());
        assert!(!registry.receive_move(envelope, TransferDomain::Actor));
        assert!(registry.receive_move(envelope, TransferDomain::Thread));
        assert_eq!(
            registry.state(region),
            Some(RuntimeOwnershipState::Local {
                owner: TransferDomain::Thread,
                generation: 1,
            })
        );
        assert!(!registry.receive_move(envelope, TransferDomain::Thread));
    }

    #[test]
    fn transport_failure_rolls_authority_back_with_new_generation() {
        let mut registry = RuntimeOwnershipRegistry::new();
        let region = registry.register_sealed_region(TransferDomain::Parent).unwrap();
        let envelope = registry
            .begin_move(region, TransferDomain::Parent, TransferDomain::Actor)
            .unwrap();
        assert!(registry.rollback_move(envelope));
        assert_eq!(
            registry.state(region),
            Some(RuntimeOwnershipState::Local {
                owner: TransferDomain::Parent,
                generation: 1,
            })
        );
        assert!(!registry.rollback_move(envelope));
    }

    #[test]
    fn process_owned_region_move_is_rejected_before_state_change() {
        let mut registry = RuntimeOwnershipRegistry::new();
        let region = registry.register_sealed_region(TransferDomain::Parent).unwrap();
        assert!(registry
            .begin_move(region, TransferDomain::Parent, TransferDomain::Process,)
            .is_none());
        assert_eq!(
            registry.state(region),
            Some(RuntimeOwnershipState::Local {
                owner: TransferDomain::Parent,
                generation: 0,
            })
        );
    }
}
