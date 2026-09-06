# HTML/CSS rendering inventory lexical false pass

Status: OPEN.

`scripts/check/check-html-css-rendering-manifest-traceability.shs:120-165` calls a tag/property rendered when its text appears in fixture HTML/CSS. It does not prove parsing, computed style, layout, Draw IR, device execution, or pixel effect. The checker’s CSS set also diverges from the 131-row executable inventory and contains claimed properties with no production owner.

Owner: web renderer inventory lane. Unblock: land `WebRenderableFeatureInventory`, classify tag/property/value-family rows honestly, bind renderable rows to production owners and focused readback evidence, generate the showcase from that inventory, and replace lexical promotion logic.

