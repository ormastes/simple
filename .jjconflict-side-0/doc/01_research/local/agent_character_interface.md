# Agent Character Interface — Research

**Date:** 2026-04-06
**Feature:** Virtual office with agent characters moving between rooms

---

## 1. Existing Infrastructure

### 1.1 Room System (Already Implemented)

**6 rooms** in `src/app/llm_dashboard/data/types.spl`:
- Research (WebFetch, WebSearch)
- Code (Read, Write, Edit, Grep, Glob, Bash)
- Skills (Skill, TaskCreate, TaskUpdate)
- Server (LSP, mcp__* tools)
- Chat (Agent communication)
- TestLab (test* tools)

Tool-to-room routing via `tool_to_room()`.

### 1.2 Agent Sprites (Already Implemented)

**TUI** (`src/app/llm_dashboard/tui/agent_sprites.spl`):
- 3x6 ASCII art characters with provider-specific heads (C=Claude, X=Codex, G=Gemini)
- Activity frames: Thinking (`*`), Reading (`]`), Writing (`>`), Searching (`?`), WebFetch (`~`), Error (`!`)
- Compact 1-char indicators for small views

**GUI** (`src/app/llm_dashboard/gui/css_sprites.spl`):
- 32x48px pixel sprites with provider colors
- CSS animations: pulse (thinking), bob (reading), sway (writing), scan (searching), shake (error)

### 1.3 Layout (Already Implemented)

- **TUI Full mode:** 2×3 room grid + agent tree + activity feed
- **TUI Compact mode:** Single-column tabbed for narrow terminals
- **GUI:** 3×2 CSS grid room layout + agent tree panel + activity feed

### 1.4 What's Missing

- Agents are NOT positioned spatially within rooms
- No movement animation between rooms
- Characters appear in tree/list views, not on the room grid
- No emote/status bubbles above characters
- No desk/furniture interaction

---

## 2. External Prior Art

### 2.1 AgentOffice (harishkotra/agent-office) ⭐43
- Phaser.js pixel sprites on tile grid
- Agents walk TO desks, approach others to talk
- Emote bubbles: 💻💬😌🔧🚶💡
- Perceive-Think-Act loop per agent
- Event bus between game canvas and React UI

### 2.2 AI Town (a16z-infra/ai-town) ⭐9.7k
- 32x32 pixel sprites with direction animation
- Tilemap world (Tiled editor, JSON export)
- Agents walk, chat, form memories
- PixiJS rendering + Convex game engine
- Based on Stanford "Generative Agents" paper

### 2.3 Pixel Agents (pablodelucca/pixel-agents) ⭐6.2k
- VSCode extension with pixel-art agents
- Activity-driven animation (matches real Claude Code activity)
- Sub-agent visualization (Task tool spawns separate characters)
- Persistent layouts saved across sessions

### 2.4 Gas Town (steveyegge/gastown) ⭐13.6k
- **TUI-based** — most relevant pattern
- Three-panel dashboard: Agent Tree | Convoy | Event Stream
- j/k scroll, Tab switch panels, 1-3 jump panels
- Coordinates Claude, Copilot, Codex, Gemini

### 2.5 Terminal Graphics Techniques

| Technique | Resolution | Support | Best For |
|-----------|-----------|---------|----------|
| ASCII art | 1×1 per cell | Universal | Simple characters |
| Emoji | ~2×1 per cell | Wide | Quick icons |
| Half-blocks ▀▄█ | 1×2 per cell | Wide | Compact sprites |
| Braille ⠿ | 2×4 per cell | Wide | Pixel art |
| Sextant | 2×3 per cell | Limited | High-res |
| Kitty protocol | Full pixel | kitty/foot | Actual images |

---

## 3. Design Direction

### 3.1 TUI: Room Map with Agent Positions

```
┌─ Research ────────┐  ┌─ Code ─────────────┐  ┌─ Skills ──────────┐
│                    │  │        [writing]    │  │                    │
│   C*   G~         │  │  C>        X*       │  │      C]            │
│  /|\  /|\         │  │ /|\       /|\       │  │     /|\            │
│  / \  / \         │  │ / \       / \       │  │     / \            │
│                    │  │                     │  │                    │
└────────────────────┘  └─────────────────────┘  └────────────────────┘
┌─ Server ──────────┐  ┌─ Chat ─────────────┐  ┌─ TestLab ─────────┐
│                    │  │  C*   →   G*        │  │   X>               │
│  X]               │  │ /|\      /|\        │  │  /|\               │
│ /|\               │  │ / \      / \        │  │  / \               │
│ / \               │  │   "discussing..."   │  │                    │
│                    │  │                     │  │                    │
└────────────────────┘  └─────────────────────┘  └────────────────────┘
```

Each agent:
- Has a position (room, x, y within room)
- Moves to the room matching their current tool use
- Shows activity-specific sprite frame
- Shows status bubble above head (optional, for focused view)

### 3.2 GUI: CSS Sprite Agents on Room Grid

- Render agent sprites inside room cards at (x,y) positions
- CSS transition for smooth movement between positions
- Emote bubbles as CSS tooltips
- Click agent to inspect details

### 3.3 Movement System

1. Agent starts in a room based on first tool use
2. When tool changes category, agent "walks" to new room:
   - TUI: instant jump (next frame shows in new room)
   - GUI: CSS transition animation (0.5s ease)
3. Position within room:
   - Hash agent_id to grid position (deterministic, no collision)
   - Or use desk slots (fixed positions per room, first-come)
4. Idle agents move to Chat room or stay in last room (dimmed)

---

## 4. Implementation Plan

### 4.1 New Files

| File | Purpose |
|------|---------|
| `data/agent_position.spl` | Position tracking, room assignment, movement logic |
| `tui/room_map.spl` | TUI room map renderer with positioned characters |
| `gui/room_map_html.spl` | GUI room map with CSS positioned sprites |

### 4.2 Modified Files

| File | Change |
|------|--------|
| `data/store.spl` | Add agent position tracking |
| `tui/app.spl` | Replace room grid with room map |
| `gui/html_views.spl` | Add room map to Agents tab |
| `gui/css_sprites.spl` | Add positioning + transition CSS |

### 4.3 Complexity: Medium

- Core logic (position tracking, movement) is simple
- TUI rendering is the main work (draw sprites at positions inside room boxes)
- GUI is straightforward (CSS absolute positioning within room divs)
