# Virtual Office Agent Programs - Visual Pattern Research

## 1. Pixel Agents (VS Code Extension by pablodelucca)

### Visual Style
- **Top-down 2D pixel art** rendered in a VS Code webview panel
- **Grid-based layout**: expandable up to 64x64 tiles
- **Character sprites**: 6 diverse top-down characters from JIK-A-4 Metro City pack
- Characters animate based on activity: typing when writing code, reading when searching files, waiting when needing input

### Room/Office Layout
- **Floor**: tiles with full HSB color control
- **Walls**: auto-tiling walls with color customization
- Built-in layout editor with tools: select, paint, erase, place, eyedropper, pick
- Export/Import as JSON files

### Furniture & Decorations
- All assets under `webview-ui/public/assets/`
- Each furniture item has its own folder with `manifest.json` declaring sprites, rotation groups, state groups (on/off), animation frames
- Floor tiles: individual PNGs in `assets/floors/`
- Wall tile sets: in `assets/walls/`
- Supports external asset directories for third-party furniture packs

### Agent Positioning
- **One agent = one character** per Claude Code terminal
- **Desks as directories** -- drag agent to desk to assign it to a project
- Speech bubbles appear when agent is waiting for input
- Sub-agents spawn as separate characters linked to parent
- Agents sit at desks; characters walk around the office

### Key Concept: "Managing AI agents feels like playing The Sims, but the results are real things built"

---

## 2. AgentOffice (harishkotra)

### Visual Style
- **Phaser.js** game canvas for pixel art rendering
- **React overlay** on top for UI panels (Chat, TaskBoard, Inspector, SystemLog, LayoutEditor)
- Top-down pixel art style

### Architecture
- `@agent-office/core`: Agent lifecycle (Perceive -> Think -> Act), **Office grid**, Task system
- `@agent-office/ui`: Phaser.js renderer + React overlay
- `@agent-office/server`: Colyseus room (multiplayer game server)

### Room Layout
- Office grid system in core package
- Agents walk to desks, think, collaborate, hire interns
- Focus mode: clicking an agent sprite follows them with smooth camera lerp
- Layout editor available as React component

### Agent Behavior (Visual)
- Agents walk around office
- Sit at desks to work
- Think (visual thought indicators)
- Collaborate face-to-face
- Execute code, search web
- Hire new team members

### Communication
- Colyseus messages for server data
- Custom EventTarget (`eventBus`) for Phaser -> React events
- Activity log, agent focus tracking

---

## 3. AI Town (a16z-infra)

### Visual Style
- **pixi-react** for client-side game rendering in browser
- Top-down 2D pixel art (RPG-style town)

### Map/World System
- Maps created with **Tiled** editor (mapeditor.org)
- Exported as JSON with 2 layers: `bgtiles` and `objmap`
- Tileset referenced as PNG spritesheets (e.g., `32x32folk.png`)
- `convertMap.js` processes Tiled JSON into engine format
- Parameters: mapDataPath, assetPath, tilesetpxw, tilesetpxh

### Character System
- Characters defined in `data/characters.ts`
- Each has: name, textureUrl (spritesheet), spritesheetData, speed
- Spritesheet typically 32x32 pixels per frame
- Characters have pathfinding toward destinations

### Room Structure
- Worlds contain many players
- Players have positions and pathfinding state
- Conversations created by proximity
- Membership states: invited -> walkingOver -> participating

### Movement
- RTS-style: specify destination, engine pathfinds
- Cannot move while in conversation (must leave first)

---

## 4. Gather.town

### Visual Style
- **Top-down 2D pixel art** (16-bit RPG aesthetic)
- **32x32 pixel** tile size for all objects
- Grid-based room layout

### Office Layout Patterns
- Templates include: welcome area, desks, co-working areas, conference rooms, break room, lunch room
- Rooms connected by corridors/doorways

### Desk System
- Base desk items: **desk, chair, computer, rug** (4 core items)
- Additional objects via Build/Mapmaker: plants, photos, books, coffee cups
- Custom images can be uploaded (keep close to 32x32 for desk items)
- Themed desks: gourmet, North Pole ice, cozy camp tent, tree stump, street ramen stand

### Desk Customization
- Ctrl+D to walk to desk
- "Customize" opens panel
- Each desk is a personal space for each user
- Items are pixel art matching the game's style

---

## 5. ASCII Art Patterns (from asciiart.eu)

### Office Scene (Harry Mason & Hayley Jane Wakenshaw, 72x19 chars)
```
::::==========::::::::::::::::::::::::::::::::::::::::::::::::::::::
:::::::=========::::::.---------------.::::::::::::::::::::::::::::::
:::=============::::::| .-----------. |:::::::::::::::::::::::::::::
::::==========::::::::| | === == == | |::::::::::::::::::::::::::::::
::::==========::::::::| | 260 ED OO | |::::::::::::::::::::::::::::
:::::::=========='::::| | urgent!   | |:::::::::::::::::::::::::::::
:::===========::::::::| |___________| |::::::((;):::::::::::::::::::
""""============""""""|___________oo__|"")"""";("""""""""""""""""""""
===========' ___)___(___,o   ( .---._
===========  |___________|   8 \ |TEA|_)     .+-------+.
===========       o8o8       ) |___|     .' |_______| `.
=============  ________8___ (  / /   \ \    |\'==========='/|
.'= --------- --`.          `.   |\ /   \ /|
|  "-----------"  |           / ooooooooooooo oo\  _\_ |
"-------------"  |          |______I_N______|  / oooooooooooo[] ooo\
```
Shows: monitor with screen content, desk surface, tea mug, IN/OUT trays, keyboard, office chair

### Worker at Workstation (Joan G. Stark, 47x31 chars)
Shows: Person sitting at desk with monitor, detailed figure with desk/chair

### Computer ASCII (small, from asciiart.eu)
```
.---------.
|.-------.|
||>run#  ||
||       ||
|"-------'|
.-^---------^-.
| ---~   AMiGA|
"-------------'
```

### Simple Computer Terminal
```
 _______
|.-----.|
|| jgs ||
||_   _||
`--)-(--`
 __[=== o]___
|:::::::::::|\ 
`-=========-`()
```

---

## 6. Unicode Box Drawing Patterns for TUI Furniture

### Box Styles Available
```
Light:    ┌─┬─┐  ├─┼─┤  │ │ │  └─┴─┘
Heavy:    ┏━┳━┓  ┣━╋━┫  ┃ ┃ ┃  ┗━┻━┛
Double:   ╔═╦═╗  ╠═╬═╣  ║ ║ ║  ╚═╩═╝
Rounded:  ╭─╮  ╰─╯
Mixed:    ╭─╥─╮  ╞═╬═╡  │ ║ │  ╰─╨─╯
```

### TUI Desk Pattern (Unicode box drawing)
```
╭─────────────╮
│ ┌─────────┐ │   Monitor
│ │ $ _     │ │   (with terminal content)
│ │         │ │
│ └─────────┘ │
│  ╭───────╮  │   Keyboard
│  ╰───────╯  │
├─────────────┤   Desk surface
│ ☕  📋  🖊  │   Items on desk
╰─────────────╯
```

### TUI Monitor (Unicode)
```
┌───────────────┐
│ ┌───────────┐ │
│ │ > compile │ │
│ │ [████░░] │ │
│ │ > done!   │ │
│ └───────────┘ │
└───────┬───────┘
        │
   ─────┴─────
```

### TUI Office Chair (Unicode)
```
  ╭───╮
  │   │
╭─┤   ├─╮
│ │   │ │
╰─┤   ├─╯
  ╰─┬─╯
  ──┼──
  ╭─┴─╮
╭─┴───┴─╮
```

---

## 7. Braille Art for Terminal Graphics

### Key Properties
- Unicode Braille characters: each character is a 2x4 dot matrix
- Effectively 2x resolution horizontally, 4x vertically compared to regular characters
- Library: **drawille** (Python) for drawing arbitrary shapes
- Also: **python-termgraphics**, **img2braille**
- Can convert images to braille text art
- Works in any terminal that supports Unicode

### Example Braille Desk (conceptual 2x4 matrix per char)
Braille gives much higher effective resolution than ASCII for smooth curves and detailed furniture.
Each character can represent 8 pixels in a 2x4 grid, making it possible to draw
detailed monitors, desks, and chairs in a compact space.

---

## 8. Recommended Patterns for Implementation

### TUI (Terminal) Approach
1. **Grid-based room**: Use Unicode box drawing for walls and room boundaries
2. **Desk unit** (approximately 5-7 chars wide, 4-5 chars tall):
   ```
   ┌─────┐
   │┌───┐│  <- Monitor
   ││ $ ││
   │└───┘│
   │ ═══ │  <- Keyboard
   ├─────┤  <- Desk edge
   └─────┘
   ```
3. **Agent at desk**: Single character (letter or emoji) positioned in front of desk
4. **Room decorations**: 
   - Plant: `🌿` or `{Y}`
   - Bookshelf: `┃▓▓▓┃` 
   - Whiteboard: `╔════╗`/`║    ║`/`╚════╝`
   - Coffee machine: `[☕]`
5. **Status indicators**: Characters next to agent showing state
   - Typing: `⌨` or `...`
   - Thinking: `💭` or `(?)`
   - Idle: `💤` or `zzz`
   - Error: `⚠` or `(!)`

### GUI/HTML/CSS Approach
1. **Grid tile system**: CSS Grid with 32x32px or 48x48px cells
2. **Top-down view** (consistent with all major projects)
3. **Sprite sheets** for characters (walking animations: 4 directions x 3-4 frames)
4. **Furniture as positioned div/img elements** on grid
5. **Z-indexing**: floor -> furniture -> characters -> UI overlays
6. **Animation**: CSS transitions for walking, keyframes for idle/working states

### Common Room Layout Pattern (all projects use this)
```
┌──────────────────────────────────────────┐
│                WHITEBOARD                │
│  ╔════════════════════════╗              │
│  ║  Sprint Board / Kanban ║              │
│  ╚════════════════════════╝              │
│                                          │
│  ┌─────┐  ┌─────┐  ┌─────┐  ┌─────┐   │
│  │Desk1│  │Desk2│  │Desk3│  │Desk4│   │  <- Row of desks
│  │ 🖥  │  │ 🖥  │  │ 🖥  │  │ 🖥  │   │
│  └──┬──┘  └──┬──┘  └──┬──┘  └──┬──┘   │
│     A        B        C        D       │  <- Agents at desks
│                                          │
│  ┌─────┐  ┌─────┐                       │
│  │Desk5│  │Desk6│    🌿    🌿          │  <- More desks + plants
│  │ 🖥  │  │ 🖥  │                       │
│  └──┬──┘  └──┬──┘                       │
│     E        F                           │
│                                          │
│  ☕ Coffee    ┃▓▓▓┃ Bookshelf           │  <- Break area
│               ┃▓▓▓┃                     │
│                                          │
│              DOOR                        │
└──────────────────────────────────────────┘
```

### Desk Variations
```
# Minimal (3x3)     # Standard (5x4)     # L-Shape (7x5)
┌───┐               ┌─────┐              ┌─────┬──┐
│ □ │               │┌───┐│              │┌───┐│  │
└───┘               ││   ││              ││   ││  │
                    │└───┘│              │└───┘│  │
                    └─────┘              └─────┴──┘
```

---

## Sources

- [Pixel Agents - GitHub](https://github.com/pablodelucca/pixel-agents)
- [Pixel Agents - VS Code Marketplace](https://marketplace.visualstudio.com/items?itemName=pablodelucca.pixel-agents)
- [AgentOffice - GitHub](https://github.com/harishkotra/agent-office)
- [AgentOffice - DEV.to Build Article](https://dev.to/harishkotra/how-i-built-agentoffice-self-growing-ai-teams-in-a-pixel-art-virtual-office-4o0p)
- [AI Town - GitHub](https://github.com/a16z-infra/ai-town)
- [AI Town Architecture](https://github.com/a16z-infra/ai-town/blob/main/ARCHITECTURE.md)
- [Gather.town Office Design](https://support.gather.town/hc/en-us/articles/15910372095508-Best-Practices-in-Office-Design)
- [Gather Custom Desk Tutorial](https://withjulio.com/gather-town-tutorial/how-to-create-custom-desk-in-gather-town-space/)
- [Gather Desk Ideas](https://withjulio.com/gather-town/5-awesome-ideas-for-your-desk-in-gather-town/)
- [ASCII Art Office - asciiart.eu](https://www.asciiart.eu/buildings-and-places/furniture/office)
- [ASCII Art Computers - asciiart.eu](https://www.asciiart.eu/computers)
- [ASCII Art Chairs - asciiart.eu](https://www.asciiart.eu/buildings-and-places/furniture/chairs)
- [Unicode Box Drawing Examples](https://gist.github.com/flaviut/0db1aec4cadf2ef06455)
- [Drawille - Braille Terminal Graphics](https://github.com/asciimoo/drawille)
- [Pixel Agents - Geeky Gadgets Review](https://www.geeky-gadgets.com/pixel-agents-vscode/)
- [Pixel Agents - Fast Company](https://www.fastcompany.com/91497413/this-charming-pixel-art-game-solves-one-of-ai-codings-most-annoying-ux-problems)
- [Christopher Johnson's ASCII Art - Chairs](https://asciiart.website/index.php?art=objects%2Ffurniture%2Fchairs)
