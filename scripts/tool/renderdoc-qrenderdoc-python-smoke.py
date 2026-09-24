#!/usr/bin/env python3
"""RenderDoc in-process Python helper.

Two modes, one file. This is the only production Python in the RenderDoc lane: the
replay API is Python-only, so this stays a thin exporter that
is invoked by a .shs wrapper and whose entire output is JSON. Nothing here classifies,
diffs, or decides - that is pure Simple in src/app/ui/renderdoc_diff/.

  smoke  (default, unchanged)  write `rdoc_qrenderdoc_python_smoke_status=pass` to
                               $RDOC_QRENDERDOC_SMOKE_OUT and exit 0.
  export ($RDOC_EXPORT_RDC set) open that capture, walk its actions, and write the
                               `renderdoc-events/v1` document to $RDOC_EXPORT_OUT.

Export contract, per event: eventId, name, type (draw/dispatch/copy/clear/present),
pipeline (graphics/compute), vs/ps/cs shader hashes, viewport, scissor, bound render
targets (id + width + height + format), draw params (vertexCount/instanceCount, or
groupsX/Y/Z for a dispatch), and outputSha256 - sha256 over the first bound graphics
colour target saved as PNG right after a draw/clear event. This is an encoded-file
digest, not a canonical pixel digest. With RDOC_EXPORT_THUMBS=1, supported single-sample
RGBA/BGRA 8-bit targets also carry a 64x64 raw RGBA8 thumbnail as base64. Unsupported
formats leave the thumbnail absent with thumbError, rather than inventing pixels.

The vs/ps/cs "hashes" are the replay API's stage index plus entry-point name, NOT a
content digest of the shader: equal values do not prove equal shader bytes. They are
informational; nothing in the diff classifies on them.

UNVERIFIED: no native RenderDoc replay was run on the authoring host (macOS).
Offline API mocks exercise the exporter contract; wrapper and diff fixture selftests
exercise separate paths. Neither is native GPU evidence.
"""
import base64
import hashlib
import json
import os
import sys

def _result_ok(result, rd):
    """Accept the legacy ResultCode and the newer ResultDetails.OK() API."""
    if isinstance(result, bool):
        return result
    ok = getattr(result, "OK", None)
    if callable(ok):
        return bool(ok())
    return result == rd.ResultCode.Succeeded


def _smoke():
    out_path = os.environ.get(
        "RDOC_QRENDERDOC_SMOKE_OUT", "build/renderdoc/qrenderdoc-python-smoke.env"
    )
    os.makedirs(os.path.dirname(out_path) or ".", exist_ok=True)
    with open(out_path, "w", encoding="utf-8") as f:
        f.write("rdoc_qrenderdoc_python_smoke_status=pass\n")
    os._exit(0)


def _event_type(action, flags_enum):
    # Debug marker names are user-controlled, not evidence of GPU work.
    if flags_enum is None:
        raise RuntimeError("ActionFlags unavailable; cannot classify capture")
    flags = int(getattr(action, "flags", 0) or 0)
    for attr, kind in (
        ("Dispatch", "dispatch"), ("Drawcall", "draw"),
        ("Clear", "clear"), ("Copy", "copy"),
        ("Resolve", "copy"), ("Present", "present"),
    ):
        bit = getattr(flags_enum, attr, None)
        if bit is not None and flags & int(bit):
            return kind
    return "other"


def _targets(controller, texture_dims):
    out = []
    try:
        state = controller.GetPipelineState()
        for res in state.GetOutputTargets():
            rid = int(res.resource)
            if rid == 0:
                continue
            width, height, fmt = texture_dims.get(rid, (0, 0, ""))
            out.append({"id": rid, "width": width, "height": height, "format": fmt})
    except Exception as exc:  # replay APIs rename across versions; report, never fake
        out.append({"id": -1, "width": 0, "height": 0, "format": "unavailable:%s" % exc})
    return out


def _shader_hashes(controller):
    hashes = {"vsHash": "", "psHash": "", "csHash": ""}
    try:
        import renderdoc as rd

        state = controller.GetPipelineState()
        for key, stage in (
            ("vsHash", rd.ShaderStage.Vertex),
            ("psHash", rd.ShaderStage.Pixel),
            ("csHash", rd.ShaderStage.Compute),
        ):
            refl = state.GetShaderReflection(stage)
            if refl is not None:
                hashes[key] = "%x" % int(getattr(refl, "stageIndex", 0)) + str(
                    getattr(refl, "entryPoint", "")
                )
    except Exception:
        pass
    return hashes


def _viewport_scissor(controller):
    viewport = ""
    scissor = ""
    try:
        state = controller.GetPipelineState()
        vps = state.GetViewports()
        if vps:
            v = vps[0]
            viewport = "%g,%g,%g,%g" % (v.x, v.y, v.width, v.height)
        scs = state.GetScissors()
        if scs:
            s = scs[0]
            scissor = "%d,%d,%d,%d" % (s.x, s.y, s.width, s.height)
    except Exception:
        pass
    return viewport, scissor


def _save_target_png(controller, rd, resource_id, path):
    save = rd.TextureSave()
    save.resourceId = resource_id
    save.destType = rd.FileType.PNG
    save.mip = 0
    save.slice.sliceIndex = 0
    save.alpha = rd.AlphaMapping.Preserve
    save.comp.blackPoint = 0.0
    save.comp.whitePoint = 1.0
    # Never let a failed save reuse the preceding action's image.
    os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
    if os.path.exists(path):
        os.remove(path)
    result = controller.SaveTexture(save, path)
    if not _result_ok(result, rd):
        raise RuntimeError("SaveTexture failed: %s" % result)
    with open(path, "rb") as fh:
        png = fh.read()
    if len(png) <= 8 or png[:8] != b"\x89PNG\r\n\x1a\n":
        raise RuntimeError("SaveTexture did not produce a PNG")
    return png


def _thumb_rgba8(controller, rd, resource_id, width, height, texture):
    """Diagnostic encoded-channel thumbnail; NOT a color-managed visual oracle.

    Only single-sample, single-layer regular RGBA/BGRA UNORM8 or SRGB is
    admitted. HDR, compressed, depth, typeless and ambiguous formats must use
    a separate format-aware exporter; never reinterpret or zero-pad them.
    """
    name = str(texture.format.Name())
    rgba = {"R8G8B8A8_UNORM", "R8G8B8A8_SRGB", "R8G8B8A8_UNORM_SRGB"}
    bgra = {"B8G8R8A8_UNORM", "B8G8R8A8_SRGB", "B8G8R8A8_UNORM_SRGB"}
    if name not in rgba | bgra:
        raise ValueError("unsupported thumbnail format: " + name)
    if (width <= 0 or height <= 0 or int(texture.width) != width
            or int(texture.height) != height):
        raise ValueError("invalid thumbnail dimensions")
    if (int(texture.msSamp) != 1 or int(texture.depth) != 1
            or int(texture.arraysize) != 1):
        raise ValueError("thumbnail requires resolved, single-layer 2D texture")
    raw = bytes(controller.GetTextureData(resource_id, rd.Subresource(0, 0, 0)))
    if len(raw) != width * height * 4:
        raise ValueError("unexpected texture byte count; no padding permitted")
    out = bytearray()
    for ty in range(64):
        sy = min(height - 1, (ty * height) // 64)
        for tx in range(64):
            sx = min(width - 1, (tx * width) // 64)
            off = (sy * width + sx) * 4
            pixel = raw[off:off + 4]
            if name in bgra:
                pixel = bytes((pixel[2], pixel[1], pixel[0], pixel[3]))
            out.extend(pixel)
    return base64.b64encode(bytes(out)).decode("ascii")


def _export():
    capture = os.environ["RDOC_EXPORT_RDC"]
    out_path = os.environ.get("RDOC_EXPORT_OUT", capture + ".events.json")
    want_thumbs = os.environ.get("RDOC_EXPORT_THUMBS", "0") == "1"

    os.makedirs(os.path.dirname(out_path) or ".", exist_ok=True)
    # A failed run must not leave an old successful export at the requested path.
    if os.path.exists(out_path):
        os.remove(out_path)
    import renderdoc as rd
    cap = None
    controller = None
    tmp_png = out_path + ".tmp.png"
    try:
        cap = rd.OpenCaptureFile()
        status = cap.OpenFile(capture, "rdc", None)
        if not _result_ok(status, rd):
            sys.stderr.write("renderdoc_status=blocked:open-failed %s\n" % status)
            return 2
        result = cap.OpenCapture(rd.ReplayOptions(), None)
        if isinstance(result, tuple) and len(result) >= 2:
            controller = result[1]
        if not isinstance(result, tuple) or len(result) != 2:
            raise RuntimeError("unexpected OpenCapture return contract")
        replay_status, controller = result
        if not _result_ok(replay_status, rd) or controller is None:
            sys.stderr.write("renderdoc_status=blocked:replay-failed\n")
            return 2
        return _export_events(controller, rd, capture, out_path, want_thumbs, tmp_png)
    finally:
        # Every acquired replay object is shut down, including when OpenFile,
        # OpenCapture, GetTextures, or texture metadata raises.
        try:
            if controller is not None:
                controller.Shutdown()
        finally:
            try:
                if cap is not None:
                    cap.Shutdown()
            finally:
                if os.path.exists(tmp_png):
                    os.remove(tmp_png)


def _export_events(controller, rd, capture, out_path, want_thumbs, tmp_png):

    texture_dims = {}
    texture_by_id = {}
    for tex in controller.GetTextures():
        texture_by_id[int(tex.resourceId)] = tex
        texture_dims[int(tex.resourceId)] = (
            int(tex.width), int(tex.height), str(tex.format.Name())
        )

    flags_enum = getattr(rd, "ActionFlags", None)
    events = []

    def walk(actions):
        for action in actions:
            eid = int(action.eventId)
            kind = _event_type(action, flags_enum)
            if kind == "other":
                walk(action.children)
                continue
            controller.SetFrameEvent(eid, True)
            # A graphics attachment is not a compute/copy/present destination.
            # v1 has no resource-usage graph; leave those outputs inapplicable.
            targets = _targets(controller, texture_dims) if kind in ("draw", "clear") else []
            viewport, scissor = _viewport_scissor(controller)
            sha = ""
            thumb = ""
            output_error = ""
            thumb_error = ""
            if targets and targets[0]["id"] > 0:
                rid = rd.ResourceId()
                try:
                    rid = next(bound.resource for bound in controller.GetPipelineState().GetOutputTargets()
                               if int(bound.resource) == targets[0]["id"])
                    png = _save_target_png(controller, rd, rid, tmp_png)
                    sha = hashlib.sha256(png).hexdigest()
                except Exception as exc:
                    output_error = str(exc)
                if sha and want_thumbs:
                    try:
                        thumb = _thumb_rgba8(
                            controller, rd, rid,
                            targets[0]["width"], targets[0]["height"],
                            texture_by_id[targets[0]["id"]]
                        )
                    except Exception as exc:
                        # A diagnostic thumbnail failure does not forge a hash.
                        thumb_error = str(exc)
            elif kind in ("draw", "clear"):
                output_error = "no readable color target (v1 graphics exporter)"
            row = {
                "eventId": eid,
                "name": str(action.GetName(controller.GetStructuredFile())),
                "type": kind,
                "pipeline": ("compute" if kind == "dispatch" else
                             "graphics" if kind in ("draw", "clear") else "transfer"),
                "viewport": viewport,
                "scissor": scissor,
                "targets": targets,
                "vertexCount": int(getattr(action, "numIndices", 0) or 0),
                "instanceCount": int(getattr(action, "numInstances", 0) or 0),
                "groupsX": int(getattr(action, "dispatchDimension", [0, 0, 0])[0]),
                "groupsY": int(getattr(action, "dispatchDimension", [0, 0, 0])[1]),
                "groupsZ": int(getattr(action, "dispatchDimension", [0, 0, 0])[2]),
                "outputSha256": sha,
                "outputStatus": "present" if sha else "unavailable" if output_error else "not-applicable",
                "outputError": output_error,
                "thumbError": thumb_error,
                "thumbFormat": "rgba8-64x64" if thumb else "",
                "thumbBase64": thumb,
            }
            row.update(_shader_hashes(controller))
            if kind != "other":
                events.append(row)
            walk(action.children)

    walk(controller.GetRootActions())
    valid_outputs = sum(1 for e in events if e["outputStatus"] == "present")
    output_errors = sum(1 for e in events if e["outputStatus"] == "unavailable")

    os.makedirs(os.path.dirname(out_path) or ".", exist_ok=True)
    with open(out_path, "w", encoding="utf-8") as fh:
        json.dump(
            {
                "schema": "renderdoc-events/v1",
                "capture": os.path.basename(capture),
                "events": events,
                "evidenceStatus": "ready" if valid_outputs and not output_errors else "blocked",
                "hashDomain": "png-file-bytes/v1-not-canonical-pixels",
                "comparisonScope": "graphics-event-diagnostics-only",
            },
            fh,
            indent=2,
        )
        fh.write("\n")
    if not valid_outputs or output_errors:
        sys.stderr.write("renderdoc_status=blocked:incomplete-output-evidence\n")
        return 2
    sys.stderr.write("renderdoc_status=exported events=%d\n" % len(events))
    return 0


if os.environ.get("RDOC_EXPORT_RDC"):
    os._exit(_export())
else:
    _smoke()
