# p03_demand_lifetime acceptance criteria

Status: NOT_IMPLEMENTED. Criteria precede intentional failing SSpec skeletons; no executable coverage or PASS is claimed.

## I5-P03-AC01 — register a provider without activating any artifact

- Status: NOT_IMPLEMENTED
- Requirements: REQ-001 NFR-005
- Setup: Prepare a valid sealed provider and count reads mappings initializations links decompressions scans and process starts.
- Action: Register its immutable catalog descriptor without demanding a capability.
- Observable: Require every activation counter to remain zero.

## I5-P03-AC02 — initialize only the demanded provider and reuse its admitted generation

- Status: NOT_IMPLEMENTED
- Requirements: REQ-002 REQ-011 NFR-005
- Setup: Prepare demanded and unrelated providers with distinct initialization counters.
- Action: Demand the selected capability twice through its public interface.
- Observable: Require equal results one initialization one admitted generation and zero unrelated activation.

## I5-P03-AC03 — give competing first demands one bounded admission owner

- Status: NOT_IMPLEMENTED
- Requirements: REQ-002 REQ-011
- Setup: Prepare 16 simultaneous callers and an admission barrier with a configured 5000 ms deadline.
- Action: Release competing first demands for the same provider capability.
- Observable: Require one initializer all 16 callers to receive the same generation no partial published receipt and every call to terminate within 5000 ms.

## I5-P03-AC04 — preserve the exact typed rejection for repeated and competing demand

- Status: NOT_IMPLEMENTED
- Requirements: REQ-002 REQ-012
- Setup: Prepare a provider with an incompatible ABI and observable initializer counter.
- Action: Demand its capability repeatedly and concurrently.
- Observable: Require the same typed ABI refusal for every caller and zero initialization.

## I5-P03-AC05 — leave admission unchanged when a waiting caller exhausts its budget

- Status: NOT_IMPLEMENTED
- Requirements: REQ-002 REQ-012
- Setup: Hold the admission owner before publication and configure a bounded waiter.
- Action: Demand the same capability from the waiting caller then release the owner.
- Observable: Require typed wait exhaustion without owner cancellation and successful later owner publication.

## I5-P03-AC06 — refuse close while any capability pin remains live

- Status: NOT_IMPLEMENTED
- Requirements: REQ-002 REQ-012
- Setup: Acquire two live capability pins on one admitted native generation.
- Action: Attempt close then release one pin and attempt close again.
- Observable: Require typed pinned refusal the same open generation and zero checked close invocations.

## I5-P03-AC07 — reject unknown and repeated pin releases without losing another owner pin

- Status: NOT_IMPLEMENTED
- Requirements: REQ-002 REQ-012
- Setup: Acquire two distinct pins and record the generation pin count.
- Action: Release an unknown pin then release a valid pin twice.
- Observable: Require typed unknown refusal stable remaining pin ownership and exactly one successful decrement.

## I5-P03-AC08 — close once after the last pin release and refuse late invocation

- Status: NOT_IMPLEMENTED
- Requirements: REQ-002 REQ-012
- Setup: Acquire a provider pin and prepare an invocation associated with that pin.
- Action: Release the last pin close the retained owner and attempt late invocation and repeated close.
- Observable: Require one successful checked close invocation closed-owner refusal and zero late provider effects without asserting immediate OS unmapping.

## I5-P03-AC09 — retain an open generation after failed unload so cleanup can retry

- Status: NOT_IMPLEMENTED
- Requirements: REQ-002 REQ-012
- Setup: Prepare an unpinned admitted provider whose first checked close invocation fails.
- Action: Attempt close retain the returned owner then retry close.
- Observable: Require typed close failure without losing the generation and exactly one successful final checked close invocation without asserting immediate OS unmapping.
