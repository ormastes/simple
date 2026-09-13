#!/usr/bin/env python3
"""RenderDoc in-process Python helper.

Two modes, one file. This is the ONLY Python in the RenderDoc lane: the replay API is
Python-only (see CLAUDE.md "ALL code in .spl/.shs"), so this stays a thin exporter that
is invoked by a .shs wrapper and whose entire output is JSON. Nothing here classifies,
diffs, or decides - that is pure Simple in src/app/ui/renderdoc_diff/.

  smoke  (default, unchanged)  write `rdoc_qrenderdoc_python_smoke_status=pass` to
                               $RDOC_QRENDERDOC_SMOKE_OUT and exit 0.
  export ($RDOC_EXPORT_RDC set) open that capture, walk its actions, and write the
                               `renderdoc-events/v1` document to $RDOC_EXPORT_OUT.

Export contract, per event: eventId, name, type (draw/dispatch/copy/clear/present),
pipeline (graphics/compute), vs/ps/cs shader hashes, viewport, scissor, bound render
targets (id + width + height + format), draw params (vertexCount/instanceCount, or
groupsX/Y/Z for a dispatch), and outputSha256 - sha256 over the bound colour target
saved as 8-bit RGBA PNG right after the event. With RDOC_EXPORT_THUMBS=1 each event also
carries a 64x64 RAW RGBA8 downsample as base64 (thumbFormat "rgba8-64x64"), raw rather
than PNG so the Simple consumer compares pixels without a PNG decoder.

The vs/ps/cs "hashes" are the replay API's stage index plus entry-point name, NOT a
content digest of the shader: equal values do not prove equal shader bytes. They are
informational; nothing in the diff classifies on them.

UNVERIFIED: the export branch has never run on the authoring host (macOS, no RenderDoc).
The wrapper's magic check and missing-binary path, and the whole diff, are proven by
scripts/check/check-renderdoc-web-diff.shs --selftest against hand-written fixtures.
"""
import base64
import hashlib
import json
import os
import sys

_TYPE_BY_KEYWORD = (
    ("Dispatch", "dispatch"),
    ("Draw", "draw"),
    ("Clear", "clear"),
    ("Copy", "copy"),
    ("Blit", "copy"),
    ("Resolve", "copy"),
    ("Present", "present"),
)


def _smoke():
    out_path = os.environ.get(
        "RDOC_QRENDERDOC_SMOKE_OUT", "build/renderdoc/qrenderdoc-python-smoke.env"
    )
    os.makedirs(os.path.dirname(out_path) or ".", exist_ok=True)
    with open(out_path, "w", encoding="utf-8") as f:
        f.write("rdoc_qrenderdoc_python_smoke_status=pass\n")
    os._exit(0)


def _event_type(action, flags_enum):
    name = str(getattr(action, "customName", "") or "")
    for keyword, kind in _TYPE_BY_KEYWORD:
        if keyword.lower() in name.lower():
            return kind
    flags = int(getattr(action, "flags", 0) or 0)
    if flags_enum is not None:
        for attr, kind in (
            ("Dispatch", "dispatch"),
            ("Drawcall", "draw"),
            ("Clear", "clear"),
            ("Copy", "copy"),
            ("Present", "present"),
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
    controller.SaveTexture(save, path)
    with open(path, "rb") as fh:
        return fh.read()


def _thumb_rgba8(controller, rd, resource_id, width, height):
    """64x64 RAW RGBA8 as base64 - raw so the Simple side needs no PNG decoder."""
    if width <= 0 or height <= 0:
        return ""
    try:
        sub = rd.Subresource(0, 0, 0)
        data = controller.GetTextureData(resource_id, sub)
    except Exception:
        return ""
    raw = bytes(data)
    stride = width * 4
    out = bytearray()
    for ty in range(64):
        sy = min(height - 1, (ty * height) // 64)
        for tx in range(64):
            sx = min(width - 1, (tx * width) // 64)
            off = sy * stride + sx * 4
            if off + 4 <= len(raw):
                out += raw[off:off + 4]
            else:
                out += b"\x00\x00\x00\x00"
    return base64.b64encode(bytes(out)).decode("ascii")


def _export():
    capture = os.environ["RDOC_EXPORT_RDC"]
    out_path = os.environ.get("RDOC_EXPORT_OUT", capture + ".events.json")
    want_thumbs = os.environ.get("RDOC_EXPORT_THUMBS", "0") == "1"

    import renderdoc as rd

    cap = rd.OpenCaptureFile()
    status = cap.OpenFile(capture, "rdc", None)
    if status != rd.ResultCode.Succeeded:
        sys.stderr.write("renderdoc_status=blocked:open-failed %s\n" % status)
        os._exit(2)
    result = cap.OpenCapture(rd.ReplayOptions(), None)
    controller = result[1] if isinstance(result, tuple) else result
    if controller is None:
        sys.stderr.write("renderdoc_status=blocked:replay-failed\n")
        os._exit(2)

    texture_dims = {}
    for tex in controller.GetTextures():
        texture_dims[int(tex.resourceId)] = (
            int(tex.width), int(tex.height), str(tex.format.Name())
        )

    flags_enum = getattr(rd, "ActionFlags", None)
    tmp_png = out_path + ".tmp.png"
    events = []

    def walk(actions):
        for action in actions:
            eid = int(action.eventId)
            controller.SetFrameEvent(eid, True)
            kind = _event_type(action, flags_enum)
            targets = _targets(controller, texture_dims)
            viewport, scissor = _viewport_scissor(controller)
            sha = ""
            thumb = ""
            if targets and targets[0]["id"] > 0:
                rid = rd.ResourceId()
                try:
                    rid = controller.GetPipelineState().GetOutputTargets()[0].resource
                    png = _save_target_png(controller, rd, rid, tmp_png)
                    sha = hashlib.sha256(png).hexdigest()
                    if want_thumbs:
                        thumb = _thumb_rgba8(
                            controller, rd, rid,
                            targets[0]["width"], targets[0]["height"]
                        )
                except Exception as exc:
                    sha = "unavailable:%s" % exc
            row = {
                "eventId": eid,
                "name": str(action.GetName(controller.GetStructuredFile())),
                "type": kind,
                "pipeline": "compute" if kind == "dispatch" else "graphics",
                "viewport": viewport,
                "scissor": scissor,
                "targets": targets,
                "vertexCount": int(getattr(action, "numIndices", 0) or 0),
                "instanceCount": int(getattr(action, "numInstances", 0) or 0),
                "groupsX": int(getattr(action, "dispatchDimension", [0, 0, 0])[0]),
                "groupsY": int(getattr(action, "dispatchDimension", [0, 0, 0])[1]),
                "groupsZ": int(getattr(action, "dispatchDimension", [0, 0, 0])[2]),
                "outputSha256": sha,
                "thumbFormat": "rgba8-64x64" if thumb else "",
                "thumbBase64": thumb,
            }
            row.update(_shader_hashes(controller))
            if kind != "other":
                events.append(row)
            walk(action.children)

    walk(controller.GetRootActions())
    controller.Shutdown()
    cap.Shutdown()
    if os.path.exists(tmp_png):
        os.remove(tmp_png)

    os.makedirs(os.path.dirname(out_path) or ".", exist_ok=True)
    with open(out_path, "w", encoding="utf-8") as fh:
        json.dump(
            {
                "schema": "renderdoc-events/v1",
                "capture": os.path.basename(capture),
                "events": events,
            },
            fh,
            indent=2,
        )
        fh.write("\n")
    sys.stderr.write("renderdoc_status=exported events=%d\n" % len(events))
    os._exit(0)


if os.environ.get("RDOC_EXPORT_RDC"):
    _export()
else:
    _smoke()
