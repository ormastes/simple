<!-- codex-research -->
# Domain Research: Optional Facets and Demand-Loaded Feature Packs

## Findings

### Static structural AOP is precedent, not the dynamic representation

AspectJ inter-type declarations can add members and parents, but the official guide describes introduction as static compile-time structure and notes that the weaver must control affected code. This supports Simple’s static nominal mode while arguing against using nominal inheritance for independently unloadable facets.

- https://eclipse.dev/aspectj/doc/latest/progguide/gettingstarted.html
- https://eclipse.dev/aspectj/doc/latest/progguide/implementation.html

### Lazy activation needs an explicit lifecycle state

OSGi lazy activation defers bundle activation until first use while still moving the bundle into a defined starting state and publishing lifecycle events. Simple should likewise separate catalog resolution, code loading, activation staging, and generation publication. Simple intentionally triggers lazy facet activation through explicit facet acquisition rather than arbitrary business class loading.

- https://docs.osgi.org/specification/osgi.core/7.0.0/framework.lifecycle.html

### Independent compression frames support selective loading

RFC 8878 defines Zstandard frames as independently decompressible and permits multiple frames in one file or stream. An SFM aspect pack can therefore keep its directory uncompressed while storing each SMF module or co-load cluster in an independent frame. Bounds, digest, decoded-size, and dictionary identity remain pack-manifest obligations.

- https://www.rfc-editor.org/info/rfc8878/

### Capability access should remain explicit

AspectJ allows privileged/private inter-type access, but that model conflicts with Simple’s current MDSOC tree privacy. The relevant external precedent demonstrates feasibility, not architectural fit. Simple v1 therefore uses public business contracts or explicit owner-exported capability facades and defers arbitrary private-layout access.

- https://eclipse.dev/aspectj/doc/released/progguide/language-interType.html

## Consequences for Simple

- Keep static nominal introduction compile-time-only.
- Represent optional dynamic facets as typed external witnesses/sidecars.
- Activate through an explicit lifecycle transaction with one atomic generation publication.
- Use independently framed payloads under an indexed SFM outer container.
- Treat transparent patchable activation as measurable non-zero footprint, never blanket “zero overhead.”

