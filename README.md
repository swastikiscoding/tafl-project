# NFA to DFA Converter and Visualizer

An interactive web app for converting a Non-deterministic Finite Automaton (NFA) into a Deterministic Finite Automaton (DFA) using the subset construction method, with step-by-step visualization and optional DFA minimization.

## Features

- Two input modes:
  - Table Input: Define states, alphabet, start and accept states, then fill transitions in a table.
  - Visual Builder: Build an NFA on canvas with right-click actions and drag interactions.
- Step-by-step subset construction walkthrough:
  - Shows epsilon-closure and move computations.
  - Highlights current states and transitions as the algorithm progresses.
- Multiple synchronized views:
  - NFA transition table (source)
  - DFA transition table (constructed incrementally)
  - DFA state-to-NFA-subset mapping
  - NFA and DFA graph visualizations
- Playback controls:
  - Previous, Next, and Play/Pause for conversion steps.
- Built-in sample NFAs for quick testing.
- DFA minimization section (partition refinement) with before/after graphs and minimized transition table.

## Tech Stack

- HTML5
- CSS3
- Vanilla JavaScript (no external framework)
- Canvas API for graph rendering and interactions

## Project Structure

- `index.html` - App layout, controls, sections, and canvas containers
- `style.css` - Theme, layout, component styling, and responsive behavior
- `script.js` - NFA/DFA logic, subset construction steps, rendering, and UI behavior
- `scripts/` - Reserved for future modular JavaScript files
- `styles/` - Reserved for future modular stylesheet files

## Getting Started

1. Clone or download this repository.
2. Open the project folder.
3. Run the app in one of these ways:
   - Open `index.html` directly in your browser, or
   - Use a local static server (recommended for development), for example with VS Code Live Server.

## How to Use

### 1. Choose Input Mode

- Table Input:
  - Enter states, alphabet, start state, and accept states.
  - Click Generate Transition Table.
  - Fill transitions (comma-separated targets, blank for none).
  - Use epsilon transitions through the epsilon column when present.
- Visual Builder:
  - Right-click canvas to add states.
  - Right-click a state for state/transition actions.
  - Drag states to arrange layout.

### 2. Convert to DFA

- Click Convert to DFA.
- Use Prev, Next, or Play/Pause to inspect each subset construction step.
- Review the generated DFA table, subset mapping, and graph.

### 3. Minimize DFA

- After conversion, click Minimize DFA.
- Compare original DFA and minimized DFA in side-by-side views.

## Example Workflows

- Load Example 1: Language ending with `ab`
- Load Example 2: Epsilon-NFA sample
- Load Example 3: Language containing `aa`

These examples are built in and available from the input section.

## Notes

- Input tokens are comma-separated for states/alphabet/transition targets.
- The app treats empty transitions as no edge.
- Dead states may be introduced during subset construction when no NFA state is reachable for a symbol.
