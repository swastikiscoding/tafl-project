(function () {
  'use strict';

  const NODE_R = 38;
  const GW = 800, GH = 520, MARGIN = 90;

  const COLORS = {
    bg: '#2B2621', nodeFill: '#221F1B', nodeStroke: '#4F453A',
    startStroke: '#E07A46', acceptStroke: '#6DA368',
    currentStroke: '#E2AD48', currentFill: '#352A16',
    deadStroke: '#C7625B', deadFill: '#3E1E1C',
    edge: '#7D7569', edgeHl: '#E2AD48', labelBg: '#221F1B',
    text: '#F2EFE9', textMuted: '#A8A196', textDim: '#7D7569',
    startArrow: '#E07A46'
  };

  // ==================== EXAMPLES ====================
  const EXAMPLES = [
    {
      states: 'q0, q1, q2', alphabet: 'a, b', start: 'q0', accept: 'q2',
      table: { q0: { a: 'q0,q1', b: 'q0', eps: '' }, q1: { a: '', b: 'q2', eps: '' }, q2: { a: '', b: '', eps: '' } }
    },
    {
      states: 'q0, q1, q2', alphabet: 'a, b', start: 'q0', accept: 'q2',
      table: { q0: { a: 'q0', b: '', eps: 'q1' }, q1: { a: '', b: 'q1,q2', eps: '' }, q2: { a: '', b: '', eps: '' } }
    },
    {
      states: 'q0, q1, q2', alphabet: 'a, b', start: 'q0', accept: 'q2',
      table: { q0: { a: 'q0,q1', b: 'q0', eps: '' }, q1: { a: 'q2', b: '', eps: '' }, q2: { a: 'q2', b: 'q2', eps: '' } }
    }
  ];

  // ==================== NFA CLASS ====================
  class NFA {
    constructor(states, alphabet, transitions, startState, acceptStates) {
      this.states = states;
      this.alphabet = alphabet;
      this.transitions = transitions;
      this.startState = startState;
      this.acceptStates = new Set(acceptStates);
    }
    epsilonClosure(stateSet) {
      const closure = new Set(stateSet);
      const stack = [...stateSet];
      while (stack.length > 0) {
        const s = stack.pop();
        for (const t of this.transitions) {
          if (t.from === s && t.symbol === 'eps' && !closure.has(t.to)) {
            closure.add(t.to); stack.push(t.to);
          }
        }
      }
      return closure;
    }
    move(stateSet, symbol) {
      const result = new Set();
      for (const s of stateSet)
        for (const t of this.transitions)
          if (t.from === s && t.symbol === symbol) result.add(t.to);
      return result;
    }
  }

  // ==================== SUBSET CONSTRUCTION ====================
  function subsetConstruct(nfa) {
    const steps = [];
    const dfaStates = [];
    const dfaTransitions = [];
    const stateMap = new Map();
    let counter = 0;
    let stepNum = 0;

    function stateKey(set) { return [...set].sort().join(','); }
    function setStr(set) { return '{' + [...set].sort().join(', ') + '}'; }
    function snap() {
      return {
        states: dfaStates.map(s => ({ ...s, nfaStates: new Set(s.nfaStates) })),
        transitions: dfaTransitions.map(t => ({ ...t }))
      };
    }
    function getOrCreate(nfaSet) {
      const key = stateKey(nfaSet);
      if (stateMap.has(key)) return { id: stateMap.get(key), isNew: false };
      const id = 'D' + counter++;
      stateMap.set(key, id);
      const isAccept = [...nfaSet].some(s => nfa.acceptStates.has(s));
      dfaStates.push({ id, nfaStates: new Set(nfaSet), isAccept, isStart: dfaStates.length === 0, isDead: nfaSet.size === 0 });
      return { id, isNew: true };
    }

    // Helper: trace epsilon-closure path for explanation
    function traceEpsilonClosure(stateSet) {
      const closure = new Set(stateSet);
      const stack = [...stateSet];
      const traceSteps = [];
      traceSteps.push('Start with: ' + setStr(stateSet));
      while (stack.length > 0) {
        const s = stack.pop();
        for (const t of nfa.transitions) {
          if (t.from === s && t.symbol === 'eps' && !closure.has(t.to)) {
            closure.add(t.to);
            stack.push(t.to);
            traceSteps.push(s + ' →ε→ ' + t.to + '  (added ' + t.to + ' to closure)');
          }
        }
      }
      if (traceSteps.length === 1) {
        traceSteps.push('No ε-transitions found — closure is unchanged');
      }
      return { closure, traceSteps };
    }

    // Helper: trace move() for explanation
    function traceMove(stateSet, symbol) {
      const result = new Set();
      const traceSteps = [];
      for (const s of stateSet) {
        const targets = [];
        for (const t of nfa.transitions) {
          if (t.from === s && t.symbol === symbol) {
            result.add(t.to);
            targets.push(t.to);
          }
        }
        if (targets.length > 0) {
          traceSteps.push('δ(' + s + ', ' + symbol + ') = {' + targets.join(', ') + '}');
        } else {
          traceSteps.push('δ(' + s + ', ' + symbol + ') = ∅  (no transition)');
        }
      }
      return { result, traceSteps };
    }

    // Step 0: Introduction
    stepNum++;
    steps.push({
      stepType: 'init',
      stepNumber: stepNum,
      title: 'Initialize Subset Construction',
      points: [
        { icon: 'info', text: 'The subset construction algorithm converts an NFA to an equivalent DFA.' },
        { icon: 'algo', text: 'Key idea: Each DFA state represents a set (subset) of NFA states.' },
        { icon: 'note', text: 'NFA has ' + nfa.states.length + ' states: ' + setStr(new Set(nfa.states)) + ', alphabet: {' + nfa.alphabet.join(', ') + '}' },
        { icon: 'next', text: 'First, we compute the ε-closure of the start state ' + nfa.startState + '.' }
      ],
      desc: 'Starting subset construction.',
      detail: '',
      snap: snap(), current: null, symbol: null, hlNfa: new Set(), hlTrans: null, tableRows: []
    });

    // Step 1: Epsilon-closure of start state
    const startTrace = traceEpsilonClosure(new Set([nfa.startState]));
    const startClosure = startTrace.closure;
    const startRes = getOrCreate(startClosure);

    stepNum++;
    const startPoints = [
      { icon: 'formula', text: 'ε-closure({' + nfa.startState + '}) = ' + setStr(startClosure) },
    ];
    for (const ts of startTrace.traceSteps) {
      startPoints.push({ icon: 'trace', text: ts });
    }
    startPoints.push({ icon: 'result', text: 'Creates DFA state ' + startRes.id + ' = ' + setStr(startClosure) });
    if (dfaStates[0].isAccept) {
      startPoints.push({ icon: 'accept', text: startRes.id + ' contains accept state(s) → marked as accepting' });
    }
    startPoints.push({ icon: 'queue', text: 'Worklist: [' + startRes.id + '] — we must process this state next.' });

    steps.push({
      stepType: 'epsilon',
      stepNumber: stepNum,
      title: 'ε-Closure of Start State',
      points: startPoints,
      desc: 'ε-closure({' + nfa.startState + '}) = ' + setStr(startClosure),
      detail: 'DFA state ' + startRes.id + (dfaStates[0].isAccept ? ' (accepting)' : ''),
      snap: snap(), current: startRes.id, symbol: null, hlNfa: new Set(startClosure), hlTrans: null,
      tableRows: buildTable(dfaStates, dfaTransitions, nfa.alphabet, startRes.id, null)
    });

    const queue = [0];
    const processed = new Set();
    while (queue.length > 0) {
      const idx = queue.shift();
      const ds = dfaStates[idx];
      if (processed.has(ds.id)) continue;
      processed.add(ds.id);

      // Add a "processing state" step
      stepNum++;
      const remaining = queue.map(i => dfaStates[i].id).filter(id => !processed.has(id));
      steps.push({
        stepType: 'process',
        stepNumber: stepNum,
        title: 'Processing DFA State ' + ds.id,
        points: [
          { icon: 'state', text: ds.id + ' = ' + setStr(ds.nfaStates) },
          { icon: 'algo', text: 'For each input symbol, compute move() then ε-closure() to find transitions.' },
          { icon: 'queue', text: 'Remaining unprocessed states: ' + (remaining.length > 0 ? '[' + remaining.join(', ') + ']' : 'none') },
          { icon: 'next', text: 'Will compute transitions for symbols: ' + nfa.alphabet.join(', ') }
        ],
        desc: 'Processing ' + ds.id + ' = ' + setStr(ds.nfaStates),
        detail: 'Computing transitions for each input symbol.',
        snap: snap(), current: ds.id, symbol: null, hlNfa: new Set(ds.nfaStates), hlTrans: null,
        tableRows: buildTable(dfaStates, dfaTransitions, nfa.alphabet, ds.id, null)
      });

      for (const sym of nfa.alphabet) {
        // Trace the move
        const moveTrace = traceMove(ds.nfaStates, sym);
        const moveRes = moveTrace.result;
        // Trace the epsilon-closure
        const closureTrace = traceEpsilonClosure(moveRes);
        const closure = closureTrace.closure;
        const res = getOrCreate(closure);
        if (res.isNew) queue.push(dfaStates.length - 1);
        dfaTransitions.push({ from: ds.id, to: res.id, symbol: sym });
        const target = dfaStates.find(s => s.id === res.id);

        stepNum++;
        const transPoints = [
          { icon: 'formula', text: 'Computing δ(' + ds.id + ', ' + sym + ')  where ' + ds.id + ' = ' + setStr(ds.nfaStates) }
        ];

        // Step A: move() breakdown
        transPoints.push({ icon: 'step', text: 'Step A — move(' + setStr(ds.nfaStates) + ', ' + sym + '):' });
        for (const ts of moveTrace.traceSteps) {
          transPoints.push({ icon: 'trace', text: ts });
        }
        transPoints.push({ icon: 'result', text: 'move result = ' + setStr(moveRes) });

        // Step B: epsilon-closure breakdown
        transPoints.push({ icon: 'step', text: 'Step B — ε-closure(' + setStr(moveRes) + '):' });
        for (const ts of closureTrace.traceSteps) {
          transPoints.push({ icon: 'trace', text: ts });
        }
        transPoints.push({ icon: 'result', text: 'ε-closure result = ' + setStr(closure) });

        // Step C: result
        if (closure.size === 0) {
          transPoints.push({ icon: 'dead', text: 'Empty set → Dead state (' + res.id + '). No NFA states reachable.' });
        } else if (res.isNew) {
          transPoints.push({ icon: 'new', text: 'New DFA state ' + res.id + ' = ' + setStr(closure) + ' discovered!' });
          if (target.isAccept) {
            transPoints.push({ icon: 'accept', text: res.id + ' contains accept state(s) → marked as accepting' });
          }
        } else {
          transPoints.push({ icon: 'existing', text: setStr(closure) + ' already exists as ' + res.id + ' — reusing.' });
        }
        transPoints.push({ icon: 'transition', text: 'Add transition: ' + ds.id + ' —' + sym + '→ ' + res.id });

        steps.push({
          stepType: 'transition',
          stepNumber: stepNum,
          title: 'Transition: δ(' + ds.id + ', ' + sym + ') → ' + res.id,
          points: transPoints,
          desc: 'δ(' + ds.id + ', ' + sym + '): move(' + setStr(ds.nfaStates) + ', ' + sym + ') = ' + setStr(moveRes),
          detail: 'ε-closure(' + setStr(moveRes) + ') = ' + setStr(closure) + ' → ' + res.id +
            (res.isNew ? ' [NEW]' : '') + (target.isDead ? ' (dead)' : '') + (target.isAccept ? ' (accepting)' : ''),
          snap: snap(), current: ds.id, symbol: sym, hlNfa: new Set(closure),
          hlTrans: { from: ds.id, to: res.id },
          tableRows: buildTable(dfaStates, dfaTransitions, nfa.alphabet, ds.id, sym)
        });
      }
    }

    // Final step
    stepNum++;
    const finalAcceptStates = dfaStates.filter(s => s.isAccept).map(s => s.id);
    const finalDeadStates = dfaStates.filter(s => s.isDead).map(s => s.id);
    const finalPoints = [
      { icon: 'done', text: 'All DFA states have been processed. No new states in the worklist.' },
      { icon: 'result', text: 'Total DFA states: ' + dfaStates.length + '   |   Total transitions: ' + dfaTransitions.length },
      { icon: 'state', text: 'Start state: ' + dfaStates[0].id + ' = ' + setStr(dfaStates[0].nfaStates) },
    ];
    if (finalAcceptStates.length > 0) {
      finalPoints.push({ icon: 'accept', text: 'Accept states: ' + finalAcceptStates.join(', ') });
    }
    if (finalDeadStates.length > 0) {
      finalPoints.push({ icon: 'dead', text: 'Dead states (trap): ' + finalDeadStates.join(', ') });
    }
    finalPoints.push({ icon: 'info', text: 'The resulting DFA recognizes the same language as the original NFA.' });

    steps.push({
      stepType: 'complete',
      stepNumber: stepNum,
      title: 'Subset Construction Complete ✓',
      points: finalPoints,
      desc: 'Subset construction complete.',
      detail: 'DFA has ' + dfaStates.length + ' states and ' + dfaTransitions.length + ' transitions.',
      snap: snap(), current: null, symbol: null, hlNfa: new Set(), hlTrans: null,
      tableRows: buildTable(dfaStates, dfaTransitions, nfa.alphabet, null, null)
    });
    return steps;
  }

  function buildTable(states, transitions, alphabet, currentState, currentSymbol) {
    return states.map(s => {
      const row = { state: s.id, subset: '{' + [...s.nfaStates].sort().join(', ') + '}', isAccept: s.isAccept, isStart: s.isStart, isDead: s.isDead, isCurrent: s.id === currentState, transitions: {} };
      for (const sym of alphabet) {
        const t = transitions.find(tr => tr.from === s.id && tr.symbol === sym);
        row.transitions[sym] = t ? { target: t.target || t.to, isHighlight: s.id === currentState && sym === currentSymbol } : null;
      }
      return row;
    });
  }

  // ==================== LAYOUT ====================
  function polygonLayout(stateIds, startId, w, h) {
    const n = stateIds.length;
    const pos = {};
    if (n === 0) return pos;
    const cx = w / 2, cy = h / 2;
    if (n === 1) { pos[stateIds[0]] = { x: cx, y: cy }; return pos; }
    if (n === 2) {
      const gap = Math.min(w, h) * 0.35;
      pos[stateIds[0]] = { x: cx - gap, y: cy };
      pos[stateIds[1]] = { x: cx + gap, y: cy };
      return pos;
    }
    const ordered = [startId, ...stateIds.filter(s => s !== startId)];
    const r = Math.min(w - 2 * MARGIN, h - 2 * MARGIN) / 2;
    for (let i = 0; i < n; i++) {
      const angle = Math.PI + (2 * Math.PI * i) / n;
      pos[ordered[i]] = { x: cx + r * Math.cos(angle), y: cy + r * Math.sin(angle) };
    }
    return pos;
  }

  function circularLayout(states, startState, w, h) {
    return polygonLayout(states, startState, w, h);
  }

  // ==================== CANVAS GRAPH ====================
  class CanvasGraph {
    constructor(canvasId) {
      this.canvas = document.getElementById(canvasId);
      this.ctx = this.canvas.getContext('2d');
      this.transform = { x: 0, y: 0, scale: 1 };
      this.dragging = false;
      this.lastMouse = { x: 0, y: 0 };
      this.data = null;
      this.dpr = window.devicePixelRatio || 1;
      this.width = 0; this.height = 0;
      this._setupEvents();
      this.resize();
    }

    _setupEvents() {
      const c = this.canvas;
      c.addEventListener('wheel', e => {
        e.preventDefault();
        const rect = c.getBoundingClientRect();
        const mx = e.clientX - rect.left, my = e.clientY - rect.top;
        const zoom = e.deltaY < 0 ? 1.1 : 0.9;
        this.transform.x = mx - (mx - this.transform.x) * zoom;
        this.transform.y = my - (my - this.transform.y) * zoom;
        this.transform.scale = Math.max(0.2, Math.min(4, this.transform.scale * zoom));
        this.render();
      }, { passive: false });

      c.addEventListener('mousedown', e => {
        this.dragging = true;
        this.lastMouse = { x: e.clientX, y: e.clientY };
      });
      c.addEventListener('mousemove', e => {
        if (!this.dragging) return;
        this.transform.x += e.clientX - this.lastMouse.x;
        this.transform.y += e.clientY - this.lastMouse.y;
        this.lastMouse = { x: e.clientX, y: e.clientY };
        this.render();
      });
      c.addEventListener('mouseup', () => { this.dragging = false; });
      c.addEventListener('mouseleave', () => { this.dragging = false; });
      window.addEventListener('resize', () => this.resize());
    }

    resize() {
      const wrap = this.canvas.parentElement;
      const rect = wrap.getBoundingClientRect();
      this.width = rect.width;
      this.height = rect.height;
      this.canvas.width = rect.width * this.dpr;
      this.canvas.height = rect.height * this.dpr;
      this.canvas.style.width = rect.width + 'px';
      this.canvas.style.height = rect.height + 'px';
      this.resetView();
      this.render();
    }

    resetView() {
      const sx = this.width / GW, sy = this.height / GH;
      const s = Math.min(sx, sy) * 0.92;
      this.transform = { x: (this.width - GW * s) / 2, y: (this.height - GH * s) / 2, scale: s };
    }

    setData(data) {
      this.data = data;
      this.resetView();
      this.render();
    }

    render() {
      const ctx = this.ctx;
      const dpr = this.dpr;
      ctx.setTransform(1, 0, 0, 1, 0, 0);
      ctx.clearRect(0, 0, this.canvas.width, this.canvas.height);
      ctx.fillStyle = COLORS.bg;
      ctx.fillRect(0, 0, this.canvas.width, this.canvas.height);
      if (!this.data || !this.data.states || this.data.states.length === 0) {
        ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
        ctx.fillStyle = COLORS.textDim;
        ctx.font = '15px Inter, sans-serif';
        ctx.textAlign = 'center';
        ctx.fillText(this.data && this.data.isDFA ? 'DFA will appear here as steps progress.' : 'No NFA loaded.', this.width / 2, this.height / 2);
        return;
      }
      ctx.setTransform(dpr * this.transform.scale, 0, 0, dpr * this.transform.scale, dpr * this.transform.x, dpr * this.transform.y);
      this._drawEdges(ctx);
      this._drawNodes(ctx);
    }

    _groupEdges() {
      const map = new Map();
      for (const t of this.data.transitions) {
        const key = t.from + '->' + t.to;
        if (!map.has(key)) map.set(key, { from: t.from, to: t.to, labels: [] });
        const labels = map.get(key).labels;
        if (!labels.includes(t.symbol)) labels.push(t.symbol);
      }
      return map;
    }

    _drawEdges(ctx) {
      const d = this.data;
      const edgeMap = this._groupEdges();
      const hlTrans = d.hlTrans;

      // Start arrow
      if (d.startState && d.positions[d.startState]) {
        const p = d.positions[d.startState];
        const len = 55;
        ctx.beginPath();
        ctx.moveTo(p.x - NODE_R - len, p.y);
        ctx.lineTo(p.x - NODE_R - 2, p.y);
        ctx.strokeStyle = COLORS.startArrow;
        ctx.lineWidth = 2.5;
        ctx.stroke();
        this._arrowhead(ctx, p.x - NODE_R - 2, p.y, 0, 12, COLORS.startArrow);
      }

      for (const [, edge] of edgeMap) {
        const fp = d.positions[edge.from], tp = d.positions[edge.to];
        if (!fp || !tp) continue;
        const label = edge.labels.join(' | ');
        const isHl = hlTrans && hlTrans.from === edge.from && hlTrans.to === edge.to;
        const color = isHl ? COLORS.edgeHl : COLORS.edge;
        const lw = isHl ? 3 : 2;

        if (edge.from === edge.to) {
          this._drawSelfLoop(ctx, fp.x, fp.y, label, color, lw);
        } else {
          const revKey = edge.to + '->' + edge.from;
          const curve = edgeMap.has(revKey) ? 38 : 0;
          this._drawCurvedEdge(ctx, fp, tp, label, curve, color, lw);
        }
      }
    }

    _drawCurvedEdge(ctx, from, to, label, curveAmt, color, lw) {
      const dx = to.x - from.x, dy = to.y - from.y;
      const dist = Math.sqrt(dx * dx + dy * dy);
      if (dist < 1) return;
      const ux = dx / dist, uy = dy / dist;
      const px = -uy, py = ux;

      const mx = (from.x + to.x) / 2 + px * curveAmt;
      const my = (from.y + to.y) / 2 + py * curveAmt;

      const acx = mx - from.x, acy = my - from.y, acd = Math.sqrt(acx * acx + acy * acy);
      const sx = from.x + NODE_R * acx / acd, sy = from.y + NODE_R * acy / acd;

      const bcx = mx - to.x, bcy = my - to.y, bcd = Math.sqrt(bcx * bcx + bcy * bcy);
      const ex = to.x + NODE_R * bcx / bcd, ey = to.y + NODE_R * bcy / bcd;

      ctx.beginPath();
      ctx.moveTo(sx, sy);
      ctx.quadraticCurveTo(mx, my, ex, ey);
      ctx.strokeStyle = color;
      ctx.lineWidth = lw;
      ctx.stroke();

      const angle = Math.atan2(ey - my, ex - mx);
      this._arrowhead(ctx, ex, ey, angle, 13, color);

      const lx = (sx + 2 * mx + ex) / 4;
      const ly = (sy + 2 * my + ey) / 4;
      this._edgeLabel(ctx, label, lx, ly);
    }

    _drawSelfLoop(ctx, x, y, label, color, lw) {
      const lr = 26;
      const sa = -Math.PI / 2 - Math.PI / 5;
      const ea = -Math.PI / 2 + Math.PI / 5;
      const sx = x + NODE_R * Math.cos(sa), sy = y + NODE_R * Math.sin(sa);
      const ex = x + NODE_R * Math.cos(ea), ey = y + NODE_R * Math.sin(ea);
      const cp1x = x - lr * 2, cp1y = y - NODE_R - lr * 3;
      const cp2x = x + lr * 2, cp2y = y - NODE_R - lr * 3;

      ctx.beginPath();
      ctx.moveTo(sx, sy);
      ctx.bezierCurveTo(cp1x, cp1y, cp2x, cp2y, ex, ey);
      ctx.strokeStyle = color;
      ctx.lineWidth = lw;
      ctx.stroke();

      const angle = Math.atan2(ey - cp2y, ex - cp2x);
      this._arrowhead(ctx, ex, ey, angle, 13, color);
      this._edgeLabel(ctx, label, x, y - NODE_R - lr * 2.5);
    }

    _arrowhead(ctx, tipX, tipY, angle, size, color) {
      ctx.fillStyle = color;
      ctx.beginPath();
      ctx.moveTo(tipX, tipY);
      ctx.lineTo(tipX - size * Math.cos(angle - 0.45), tipY - size * Math.sin(angle - 0.45));
      ctx.lineTo(tipX - size * Math.cos(angle + 0.45), tipY - size * Math.sin(angle + 0.45));
      ctx.closePath();
      ctx.fill();
    }

    _edgeLabel(ctx, text, x, y) {
      ctx.font = '600 14px JetBrains Mono, monospace';
      const tw = ctx.measureText(text).width + 14;
      ctx.fillStyle = COLORS.labelBg;
      ctx.beginPath();
      ctx.roundRect(x - tw / 2, y - 11, tw, 22, 4);
      ctx.fill();
      ctx.fillStyle = COLORS.text;
      ctx.textAlign = 'center';
      ctx.textBaseline = 'middle';
      ctx.fillText(text, x, y);
    }

    _drawNodes(ctx) {
      const d = this.data;
      for (const stateId of d.states) {
        const p = d.positions[stateId];
        if (!p) continue;
        const isAccept = d.acceptStates.has(stateId);
        const isStart = stateId === d.startState;
        const isCurrent = d.hlStates && d.hlStates.has(stateId);
        const sd = d.isDFA ? (d.stateData || []).find(s => s.id === stateId) : null;
        const isDead = sd ? sd.isDead : false;

        let fill = COLORS.nodeFill, stroke = COLORS.nodeStroke;
        if (isDead) { stroke = COLORS.deadStroke; fill = COLORS.deadFill; }
        else if (isCurrent) { stroke = COLORS.currentStroke; fill = COLORS.currentFill; }
        else if (isAccept) { stroke = COLORS.acceptStroke; }
        else if (isStart) { stroke = COLORS.startStroke; }

        // Outer circle
        ctx.beginPath();
        ctx.arc(p.x, p.y, NODE_R, 0, 2 * Math.PI);
        ctx.fillStyle = fill;
        ctx.fill();
        ctx.strokeStyle = stroke;
        ctx.lineWidth = 2.5;
        if (isDead) ctx.setLineDash([6, 4]); else ctx.setLineDash([]);
        ctx.stroke();
        ctx.setLineDash([]);

        // Accept ring
        if (isAccept) {
          ctx.beginPath();
          ctx.arc(p.x, p.y, NODE_R - 6, 0, 2 * Math.PI);
          ctx.strokeStyle = isCurrent ? COLORS.currentStroke : COLORS.acceptStroke;
          ctx.lineWidth = 2.5;
          ctx.stroke();
        }

        // Label
        ctx.fillStyle = COLORS.text;
        ctx.font = '600 16px JetBrains Mono, monospace';
        ctx.textAlign = 'center';
        ctx.textBaseline = 'middle';
        ctx.fillText(stateId, p.x, p.y);

        // Sublabel
        if (d.isDFA && sd) {
          ctx.fillStyle = COLORS.textMuted;
          ctx.font = '400 11px JetBrains Mono, monospace';
          ctx.textAlign = 'center';
          ctx.textBaseline = 'top';
          ctx.fillText('{' + [...sd.nfaStates].sort().join(',') + '}', p.x, p.y + NODE_R + 8);
        }
      }
    }
  }

  // ==================== DFA TABLE RENDERING ====================
  function renderDFATable(rows, alphabet) {
    const head = document.getElementById('dfaTableHead');
    const body = document.getElementById('dfaTableBody');
    head.innerHTML = ''; body.innerHTML = '';
    if (!rows || rows.length === 0) return;

    const tr = document.createElement('tr');
    const headers = ['DFA State', 'NFA Subset'];
    alphabet.forEach(a => headers.push('\u03B4(_, ' + a + ')'));
    headers.forEach(h => {
      const th = document.createElement('th');
      th.textContent = h;
      tr.appendChild(th);
    });
    head.appendChild(tr);

    for (const row of rows) {
      const r = document.createElement('tr');
      if (row.isCurrent) r.classList.add('highlight-row');
      const stateCell = document.createElement('td');
      let prefix = '';
      if (row.isStart) prefix += '\u2192 ';
      if (row.isAccept) prefix += '* ';
      stateCell.textContent = prefix + row.state;
      if (row.isAccept) stateCell.classList.add('accept-cell');
      if (row.isDead) stateCell.classList.add('dead-cell');
      r.appendChild(stateCell);
      const subCell = document.createElement('td');
      subCell.textContent = row.subset;
      if (row.isDead) subCell.classList.add('dead-cell');
      r.appendChild(subCell);
      for (const sym of alphabet) {
        const td = document.createElement('td');
        const t = row.transitions[sym];
        td.textContent = t ? t.target : '--';
        if (t && t.isHighlight) td.classList.add('highlight-cell');
        r.appendChild(td);
      }
      body.appendChild(r);
    }
  }

  // ==================== DFA MINIMIZATION ====================
  function minimizeDFAAlgorithm(dfaStates, dfaTransitions, dfaStartId, dfaAcceptSet, alphabet) {
    // Step 1: remove unreachable states
    const reachable = new Set();
    const bfsQueue = [dfaStartId];
    reachable.add(dfaStartId);
    while (bfsQueue.length > 0) {
      const s = bfsQueue.shift();
      for (const t of dfaTransitions) {
        if (t.from === s && !reachable.has(t.to)) {
          reachable.add(t.to); bfsQueue.push(t.to);
        }
      }
    }
    const rStates = dfaStates.filter(s => reachable.has(s));
    const rTrans = dfaTransitions.filter(t => reachable.has(t.from) && reachable.has(t.to));

    // Step 2: initial partition — accept vs non-accept
    const acceptGroup = rStates.filter(s => dfaAcceptSet.has(s));
    const nonAcceptGroup = rStates.filter(s => !dfaAcceptSet.has(s));
    let partitions = [];
    if (nonAcceptGroup.length > 0) partitions.push(new Set(nonAcceptGroup));
    if (acceptGroup.length > 0) partitions.push(new Set(acceptGroup));

    function getTarget(state, sym) {
      const t = rTrans.find(tr => tr.from === state && tr.symbol === sym);
      return t ? t.to : null;
    }
    function getPartIdx(state) {
      for (let i = 0; i < partitions.length; i++) if (partitions[i].has(state)) return i;
      return -1;
    }

    // Step 3: refine
    let changed = true;
    while (changed) {
      changed = false;
      const next = [];
      for (const group of partitions) {
        if (group.size <= 1) { next.push(group); continue; }
        const sigs = new Map();
        for (const st of group) {
          const sig = alphabet.map(sym => {
            const tgt = getTarget(st, sym);
            return tgt !== null ? getPartIdx(tgt) : -1;
          }).join(',');
          if (!sigs.has(sig)) sigs.set(sig, new Set());
          sigs.get(sig).add(st);
        }
        if (sigs.size > 1) changed = true;
        for (const g of sigs.values()) next.push(g);
      }
      partitions = next;
    }

    // Step 4: build minimized DFA
    const stateToP = new Map();
    for (let i = 0; i < partitions.length; i++)
      for (const s of partitions[i]) stateToP.set(s, i);

    // Sort partitions so start state's partition comes first
    const startPart = stateToP.get(dfaStartId);
    const sortedIndices = [startPart, ...Array.from({length: partitions.length}, (_, i) => i).filter(i => i !== startPart)];

    const minStates = sortedIndices.map((pi, ni) => ({
      id: 'M' + ni,
      origStates: [...partitions[pi]].sort(),
      isAccept: [...partitions[pi]].some(s => dfaAcceptSet.has(s)),
      isStart: ni === 0
    }));
    const pToMin = new Map();
    sortedIndices.forEach((pi, ni) => pToMin.set(pi, 'M' + ni));

    const minTrans = [];
    for (const ms of minStates) {
      const rep = ms.origStates[0];
      const fromP = stateToP.get(rep);
      for (const sym of alphabet) {
        const tgt = getTarget(rep, sym);
        if (tgt !== null) {
          const toP = stateToP.get(tgt);
          minTrans.push({ from: pToMin.get(fromP), to: pToMin.get(toP), symbol: sym });
        }
      }
    }

    return {
      states: minStates,
      transitions: minTrans,
      startState: 'M0',
      acceptStates: new Set(minStates.filter(s => s.isAccept).map(s => s.id))
    };
  }

  function renderMinTable(minResult, alphabet) {
    const head = document.getElementById('minDfaTableHead');
    const body = document.getElementById('minDfaTableBody');
    head.innerHTML = ''; body.innerHTML = '';

    const tr = document.createElement('tr');
    ['Min State', 'DFA States'].concat(alphabet.map(a => '\u03B4(_, ' + a + ')')).forEach(h => {
      const th = document.createElement('th'); th.textContent = h; tr.appendChild(th);
    });
    head.appendChild(tr);

    for (const ms of minResult.states) {
      const r = document.createElement('tr');
      const sc = document.createElement('td');
      let pfx = '';
      if (ms.isStart) pfx += '\u2192 ';
      if (ms.isAccept) pfx += '* ';
      sc.textContent = pfx + ms.id;
      if (ms.isAccept) sc.classList.add('accept-cell');
      r.appendChild(sc);
      const oc = document.createElement('td');
      oc.textContent = '{' + ms.origStates.join(', ') + '}';
      r.appendChild(oc);
      for (const sym of alphabet) {
        const td = document.createElement('td');
        const t = minResult.transitions.find(tr => tr.from === ms.id && tr.symbol === sym);
        td.textContent = t ? t.to : '--';
        r.appendChild(td);
      }
      body.appendChild(r);
    }
  }

  // ==================== VISUAL NFA BUILDER ====================
  class VisualNFABuilder {
    constructor(canvasId) {
      this.canvas = document.getElementById(canvasId);
      this.ctx = this.canvas.getContext('2d');
      this.nodes = [];
      this.transitions = [];
      this.nextStateNum = 0;
      this.transform = { x: 0, y: 0, scale: 1 };
      this.dragging = false;
      this.dragNode = null;
      this.panning = false;
      this.lastMouse = { x: 0, y: 0 };
      this.transitionMode = null;
      this.mouseWorld = { x: 0, y: 0 };
      this.dpr = window.devicePixelRatio || 1;
      this.width = 0;
      this.height = 0;
      this.initialized = false;
    }

    init() {
      if (this.initialized) return;
      this.initialized = true;
      this._setup();
      this.resize();
    }

    _screenToWorld(clientX, clientY) {
      const rect = this.canvas.getBoundingClientRect();
      return {
        x: (clientX - rect.left - this.transform.x) / this.transform.scale,
        y: (clientY - rect.top - this.transform.y) / this.transform.scale
      };
    }

    _hitNode(wx, wy) {
      for (let i = this.nodes.length - 1; i >= 0; i--) {
        const n = this.nodes[i];
        const dx = n.x - wx, dy = n.y - wy;
        if (dx * dx + dy * dy <= NODE_R * NODE_R) return n;
      }
      return null;
    }

    _setup() {
      const c = this.canvas;
      c.addEventListener('contextmenu', e => {
        e.preventDefault();
        const w = this._screenToWorld(e.clientX, e.clientY);
        const node = this._hitNode(w.x, w.y);
        if (this.transitionMode) { this.transitionMode = null; this.render(); return; }
        if (node) this._showNodeMenu(e.clientX, e.clientY, node);
        else this._showCanvasMenu(e.clientX, e.clientY, w);
      });

      c.addEventListener('wheel', e => {
        e.preventDefault();
        const rect = c.getBoundingClientRect();
        const mx = e.clientX - rect.left, my = e.clientY - rect.top;
        const zoom = e.deltaY < 0 ? 1.1 : 0.9;
        this.transform.x = mx - (mx - this.transform.x) * zoom;
        this.transform.y = my - (my - this.transform.y) * zoom;
        this.transform.scale = Math.max(0.2, Math.min(4, this.transform.scale * zoom));
        this.render();
      }, { passive: false });

      c.addEventListener('mousedown', e => {
        if (e.button !== 0) return;
        const w = this._screenToWorld(e.clientX, e.clientY);
        const node = this._hitNode(w.x, w.y);
        if (this.transitionMode) {
          if (node) this._askSymbol(this.transitionMode.fromId, node.id);
          this.transitionMode = null;
          this.render();
          return;
        }
        if (node) { this.dragNode = node; this.dragging = true; }
        else { this.panning = true; }
        this.lastMouse = { x: e.clientX, y: e.clientY };
      });

      c.addEventListener('mousemove', e => {
        this.mouseWorld = this._screenToWorld(e.clientX, e.clientY);
        if (this.dragging && this.dragNode) {
          this.dragNode.x = this.mouseWorld.x;
          this.dragNode.y = this.mouseWorld.y;
          this.render(); this._updateInfo();
        } else if (this.panning) {
          this.transform.x += e.clientX - this.lastMouse.x;
          this.transform.y += e.clientY - this.lastMouse.y;
          this.lastMouse = { x: e.clientX, y: e.clientY };
          this.render();
        } else if (this.transitionMode) {
          this.render();
        }
      });

      c.addEventListener('mouseup', () => { this.dragging = false; this.dragNode = null; this.panning = false; });
      c.addEventListener('mouseleave', () => { this.dragging = false; this.dragNode = null; this.panning = false; });
      window.addEventListener('resize', () => { if (this.canvas.offsetParent) this.resize(); });

      document.addEventListener('click', e => {
        const menu = document.getElementById('ctxMenu');
        if (menu && !menu.contains(e.target)) menu.style.display = 'none';
      });
    }

    _showNodeMenu(cx, cy, node) {
      const menu = document.getElementById('ctxMenu');
      menu.innerHTML = '';
      menu.style.display = 'block';
      menu.style.left = cx + 'px';
      menu.style.top = cy + 'px';

      const items = [
        { label: (node.isStart ? '✓ ' : '') + 'Start State', action: () => this.setStartState(node.id) },
        { label: (node.isAccept ? '✓ ' : '') + 'Accept State', action: () => this.toggleAccept(node.id) },
        { label: 'Add Transition from ' + node.id, action: () => { this.transitionMode = { fromId: node.id }; this.render(); } },
        { sep: true },
        { label: 'Delete ' + node.id, action: () => this.removeNode(node.id), danger: true }
      ];

      const outgoing = this.transitions.filter(t => t.from === node.id);
      if (outgoing.length > 0) {
        items.push({ sep: true });
        for (const t of outgoing)
          items.push({ label: 'Delete: ' + t.from + ' \u2014' + t.symbol + '\u2192 ' + t.to, action: () => this.removeTransition(t), danger: true });
      }

      for (const it of items) {
        if (it.sep) { const s = document.createElement('div'); s.className = 'ctx-separator'; menu.appendChild(s); continue; }
        const el = document.createElement('div');
        el.className = 'ctx-item' + (it.danger ? ' ctx-danger' : '');
        el.textContent = it.label;
        el.addEventListener('click', () => { menu.style.display = 'none'; it.action(); });
        menu.appendChild(el);
      }
    }

    _showCanvasMenu(cx, cy, worldPos) {
      const menu = document.getElementById('ctxMenu');
      menu.innerHTML = '';
      menu.style.display = 'block';
      menu.style.left = cx + 'px';
      menu.style.top = cy + 'px';
      const el = document.createElement('div');
      el.className = 'ctx-item';
      el.textContent = 'Add State (q' + this.nextStateNum + ')';
      el.addEventListener('click', () => { menu.style.display = 'none'; this.addNode(worldPos.x, worldPos.y); });
      menu.appendChild(el);
    }

    _askSymbol(fromId, toId) {
      const overlay = document.getElementById('symbolOverlay');
      const input = document.getElementById('symbolInput');
      overlay.style.display = 'flex';
      input.value = '';
      setTimeout(() => input.focus(), 50);

      const cleanup = () => {
        overlay.style.display = 'none';
        document.getElementById('symbolOk').onclick = null;
        document.getElementById('symbolCancel').onclick = null;
        document.getElementById('symbolEpsilon').onclick = null;
        input.onkeydown = null;
      };
      const submit = () => {
        const v = input.value.trim();
        if (v) {
          const symbols = v.split(',').map(s => s.trim()).filter(Boolean);
          for (const sym of symbols) this.addTransition(fromId, toId, sym);
        }
        cleanup();
      };
      const submitEps = () => { this.addTransition(fromId, toId, '\u03b5'); cleanup(); };

      document.getElementById('symbolOk').onclick = submit;
      document.getElementById('symbolCancel').onclick = cleanup;
      document.getElementById('symbolEpsilon').onclick = submitEps;
      input.onkeydown = e => { if (e.key === 'Enter') submit(); if (e.key === 'Escape') cleanup(); };
    }

    addNode(x, y) {
      const id = 'q' + this.nextStateNum++;
      this.nodes.push({ id, x, y, isStart: this.nodes.length === 0, isAccept: false });
      this.render();
      this._updateInfo();
    }

    removeNode(id) {
      this.nodes = this.nodes.filter(n => n.id !== id);
      this.transitions = this.transitions.filter(t => t.from !== id && t.to !== id);
      if (!this.nodes.some(n => n.isStart) && this.nodes.length > 0) this.nodes[0].isStart = true;
      this.render();
      this._updateInfo();
    }

    setStartState(id) {
      this.nodes.forEach(n => { n.isStart = n.id === id; });
      this.render();
      this._updateInfo();
    }

    toggleAccept(id) {
      const node = this.nodes.find(n => n.id === id);
      if (node) node.isAccept = !node.isAccept;
      this.render();
      this._updateInfo();
    }

    addTransition(from, to, symbol) {
      if (!this.transitions.some(t => t.from === from && t.to === to && t.symbol === symbol)) {
        this.transitions.push({ from, to, symbol });
      }
      this.render();
      this._updateInfo();
    }

    removeTransition(trans) {
      this.transitions = this.transitions.filter(t => t !== trans);
      this.render();
      this._updateInfo();
    }

    resetBuilder() {
      this.nodes = [];
      this.transitions = [];
      this.nextStateNum = 0;
      this.transitionMode = null;
      this.transform = { x: 0, y: 0, scale: 1 };
      this.render();
      this._updateInfo();
    }

    resize() {
      const wrap = this.canvas.parentElement;
      if (!wrap) return;
      const rect = wrap.getBoundingClientRect();
      this.width = rect.width;
      this.height = rect.height;
      this.canvas.width = rect.width * this.dpr;
      this.canvas.height = rect.height * this.dpr;
      this.canvas.style.width = rect.width + 'px';
      this.canvas.style.height = rect.height + 'px';
      this.render();
    }

    _updateInfo() {
      const el = document.getElementById('visualNfaInfo');
      if (this.nodes.length === 0) { el.classList.remove('visible'); return; }
      el.classList.add('visible');
      const states = this.nodes.map(n => n.id).join(', ');
      const alphaSet = new Set();
      for (const t of this.transitions) if (t.symbol !== '\u03b5') alphaSet.add(t.symbol);
      const alpha = [...alphaSet].sort().join(', ') || '(none)';
      const start = this.nodes.find(n => n.isStart)?.id || '(none)';
      const accept = this.nodes.filter(n => n.isAccept).map(n => n.id).join(', ') || '(none)';
      const transStr = this.transitions.map(t => '\u03b4(' + t.from + ', ' + t.symbol + ') \u2192 ' + t.to).join(' &nbsp;|&nbsp; ') || '(none)';
      el.innerHTML = '<strong class="nfa-label">Q</strong> = {' + states + '} &nbsp;&nbsp; '
        + '<strong class="nfa-label">\u03a3</strong> = {' + alpha + '} &nbsp;&nbsp; '
        + '<strong class="nfa-label">q\u2080</strong> = ' + start + ' &nbsp;&nbsp; '
        + '<strong class="nfa-label">F</strong> = {' + accept + '}<br>'
        + '<strong class="nfa-label">\u03b4</strong>: ' + transStr;
    }

    extractNFA() {
      if (this.nodes.length === 0) { alert('Please add at least one state.'); return null; }
      const startNode = this.nodes.find(n => n.isStart);
      if (!startNode) { alert('Please set a start state.'); return null; }
      if (!this.nodes.some(n => n.isAccept)) { alert('Please set at least one accept state.'); return null; }
      const states = this.nodes.map(n => n.id);
      const alphaSet = new Set();
      const transitions = [];
      for (const t of this.transitions) {
        if (t.symbol === '\u03b5') transitions.push({ from: t.from, symbol: 'eps', to: t.to });
        else { alphaSet.add(t.symbol); transitions.push({ from: t.from, symbol: t.symbol, to: t.to }); }
      }
      const alphabet = [...alphaSet].sort();
      if (alphabet.length === 0) { alert('Add at least one non-epsilon transition.'); return null; }
      return new NFA(states, alphabet, transitions, startNode.id, this.nodes.filter(n => n.isAccept).map(n => n.id));
    }

    render() {
      const ctx = this.ctx, dpr = this.dpr;
      ctx.setTransform(1, 0, 0, 1, 0, 0);
      ctx.clearRect(0, 0, this.canvas.width, this.canvas.height);
      ctx.fillStyle = COLORS.bg;
      ctx.fillRect(0, 0, this.canvas.width, this.canvas.height);

      if (this.nodes.length === 0) {
        ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
        ctx.fillStyle = COLORS.textDim;
        ctx.font = '15px Inter, sans-serif';
        ctx.textAlign = 'center';
        ctx.fillText('Right-click to add states', this.width / 2, this.height / 2 - 10);
        ctx.font = '12px Inter, sans-serif';
        ctx.fillText('Build your NFA visually', this.width / 2, this.height / 2 + 14);
        return;
      }

      ctx.setTransform(dpr * this.transform.scale, 0, 0, dpr * this.transform.scale,
        dpr * this.transform.x, dpr * this.transform.y);

      this._drawEdges(ctx);
      this._drawTransitionPreview(ctx);
      this._drawNodes(ctx);
    }

    _groupEdges() {
      const map = new Map();
      for (const t of this.transitions) {
        const key = t.from + '->' + t.to;
        if (!map.has(key)) map.set(key, { from: t.from, to: t.to, labels: [] });
        const labels = map.get(key).labels;
        if (!labels.includes(t.symbol)) labels.push(t.symbol);
      }
      return map;
    }

    _drawEdges(ctx) {
      const edgeMap = this._groupEdges();
      const startNode = this.nodes.find(n => n.isStart);
      if (startNode) {
        ctx.beginPath();
        ctx.moveTo(startNode.x - NODE_R - 55, startNode.y);
        ctx.lineTo(startNode.x - NODE_R - 2, startNode.y);
        ctx.strokeStyle = COLORS.startArrow; ctx.lineWidth = 2.5; ctx.stroke();
        this._arrowhead(ctx, startNode.x - NODE_R - 2, startNode.y, 0, 12, COLORS.startArrow);
      }
      for (const [, edge] of edgeMap) {
        const fn = this.nodes.find(n => n.id === edge.from), tn = this.nodes.find(n => n.id === edge.to);
        if (!fn || !tn) continue;
        const label = edge.labels.join(' | ');
        if (edge.from === edge.to) this._drawSelfLoop(ctx, fn.x, fn.y, label, COLORS.edge, 2);
        else {
          const revKey = edge.to + '->' + edge.from;
          this._drawCurvedEdge(ctx, fn, tn, label, edgeMap.has(revKey) ? 38 : 0, COLORS.edge, 2);
        }
      }
    }

    _drawCurvedEdge(ctx, from, to, label, curveAmt, color, lw) {
      const dx = to.x - from.x, dy = to.y - from.y;
      const dist = Math.sqrt(dx * dx + dy * dy);
      if (dist < 1) return;
      const px = -dy / dist, py = dx / dist;
      const mx = (from.x + to.x) / 2 + px * curveAmt, my = (from.y + to.y) / 2 + py * curveAmt;
      const acx = mx - from.x, acy = my - from.y, acd = Math.sqrt(acx * acx + acy * acy);
      const sx = from.x + NODE_R * acx / acd, sy = from.y + NODE_R * acy / acd;
      const bcx = mx - to.x, bcy = my - to.y, bcd = Math.sqrt(bcx * bcx + bcy * bcy);
      const ex = to.x + NODE_R * bcx / bcd, ey = to.y + NODE_R * bcy / bcd;
      ctx.beginPath(); ctx.moveTo(sx, sy); ctx.quadraticCurveTo(mx, my, ex, ey);
      ctx.strokeStyle = color; ctx.lineWidth = lw; ctx.stroke();
      this._arrowhead(ctx, ex, ey, Math.atan2(ey - my, ex - mx), 13, color);
      this._edgeLabel(ctx, label, (sx + 2 * mx + ex) / 4, (sy + 2 * my + ey) / 4);
    }

    _drawSelfLoop(ctx, x, y, label, color, lw) {
      const lr = 26;
      const sa = -Math.PI / 2 - Math.PI / 5, ea = -Math.PI / 2 + Math.PI / 5;
      const sx = x + NODE_R * Math.cos(sa), sy = y + NODE_R * Math.sin(sa);
      const ex = x + NODE_R * Math.cos(ea), ey = y + NODE_R * Math.sin(ea);
      const cp1x = x - lr * 2, cp1y = y - NODE_R - lr * 3, cp2x = x + lr * 2, cp2y = y - NODE_R - lr * 3;
      ctx.beginPath(); ctx.moveTo(sx, sy); ctx.bezierCurveTo(cp1x, cp1y, cp2x, cp2y, ex, ey);
      ctx.strokeStyle = color; ctx.lineWidth = lw; ctx.stroke();
      this._arrowhead(ctx, ex, ey, Math.atan2(ey - cp2y, ex - cp2x), 13, color);
      this._edgeLabel(ctx, label, x, y - NODE_R - lr * 2.5);
    }

    _arrowhead(ctx, tipX, tipY, angle, size, color) {
      ctx.fillStyle = color; ctx.beginPath(); ctx.moveTo(tipX, tipY);
      ctx.lineTo(tipX - size * Math.cos(angle - 0.45), tipY - size * Math.sin(angle - 0.45));
      ctx.lineTo(tipX - size * Math.cos(angle + 0.45), tipY - size * Math.sin(angle + 0.45));
      ctx.closePath(); ctx.fill();
    }

    _edgeLabel(ctx, text, x, y) {
      ctx.font = '600 14px JetBrains Mono, monospace';
      const tw = ctx.measureText(text).width + 14;
      ctx.fillStyle = COLORS.labelBg; ctx.beginPath(); ctx.roundRect(x - tw / 2, y - 11, tw, 22, 4); ctx.fill();
      ctx.fillStyle = COLORS.text; ctx.textAlign = 'center'; ctx.textBaseline = 'middle'; ctx.fillText(text, x, y);
    }

    _drawTransitionPreview(ctx) {
      if (!this.transitionMode) return;
      const fn = this.nodes.find(n => n.id === this.transitionMode.fromId);
      if (!fn) return;
      ctx.beginPath(); ctx.moveTo(fn.x, fn.y); ctx.lineTo(this.mouseWorld.x, this.mouseWorld.y);
      ctx.strokeStyle = COLORS.amber; ctx.lineWidth = 2; ctx.setLineDash([8, 4]); ctx.stroke(); ctx.setLineDash([]);
    }

    _drawNodes(ctx) {
      for (const node of this.nodes) {
        let fill = COLORS.nodeFill, stroke = COLORS.nodeStroke;
        if (node.isAccept) stroke = COLORS.acceptStroke;
        if (node.isStart) stroke = COLORS.startStroke;
        ctx.beginPath(); ctx.arc(node.x, node.y, NODE_R, 0, 2 * Math.PI);
        ctx.fillStyle = fill; ctx.fill();
        ctx.strokeStyle = stroke; ctx.lineWidth = 2.5; ctx.setLineDash([]); ctx.stroke();
        if (node.isAccept) {
          ctx.beginPath(); ctx.arc(node.x, node.y, NODE_R - 6, 0, 2 * Math.PI);
          ctx.strokeStyle = COLORS.acceptStroke; ctx.lineWidth = 2.5; ctx.stroke();
        }
        ctx.fillStyle = COLORS.text; ctx.font = '600 16px JetBrains Mono, monospace';
        ctx.textAlign = 'center'; ctx.textBaseline = 'middle'; ctx.fillText(node.id, node.x, node.y);
      }
    }
  }

  // ==================== APPLICATION ====================
  class App {
    constructor() {
      this.nfa = null;
      this.steps = [];
      this.currentStep = 0;
      this.playing = false;
      this.playTimer = null;
      this.nfaGraph = null;
      this.dfaGraph = null;
      this.visualBuilder = null;
      this.inputMode = 'table';
    }

    switchMode(mode) {
      this.inputMode = mode;
      document.getElementById('tableModePanel').style.display = mode === 'table' ? '' : 'none';
      document.getElementById('visualModePanel').style.display = mode === 'visual' ? '' : 'none';
      document.getElementById('tableModeBtn').classList.toggle('active', mode === 'table');
      document.getElementById('visualModeBtn').classList.toggle('active', mode === 'visual');
      if (mode === 'visual') {
        if (!this.visualBuilder) {
          this.visualBuilder = new VisualNFABuilder('nfaBuilderCanvas');
        }
        this.visualBuilder.init();
        setTimeout(() => this.visualBuilder.resize(), 50);
      }
    }

    convertVisualNFA() {
      if (!this.visualBuilder) return;
      const nfa = this.visualBuilder.extractNFA();
      if (!nfa) return;
      this.nfa = nfa;
      this.steps = subsetConstruct(nfa);
      this.currentStep = 0;
      this.playing = false;
      document.getElementById('inputSection').style.display = 'none';
      document.getElementById('vizSection').style.display = '';
      this.nfaGraph = new CanvasGraph('nfaCanvas');
      this.dfaGraph = new CanvasGraph('dfaCanvas');
      this.renderStep();
    }

    loadExample(idx) {
      const ex = EXAMPLES[idx];
      document.getElementById('statesInput').value = ex.states;
      document.getElementById('alphabetInput').value = ex.alphabet;
      document.getElementById('startInput').value = ex.start;
      document.getElementById('acceptInput').value = ex.accept;
      this.generateNFATable();
      // Fill table cells
      const states = ex.states.split(',').map(s => s.trim()).filter(Boolean);
      const alphabet = ex.alphabet.split(',').map(s => s.trim()).filter(Boolean);
      const syms = [...alphabet, 'eps'];
      for (const st of states) {
        for (const sym of syms) {
          const input = document.getElementById('nfa_' + st + '_' + sym);
          if (input && ex.table[st] && ex.table[st][sym] !== undefined) {
            input.value = ex.table[st][sym];
          }
        }
      }
    }

    generateNFATable() {
      const states = document.getElementById('statesInput').value.split(',').map(s => s.trim()).filter(Boolean);
      const alphabet = document.getElementById('alphabetInput').value.split(',').map(s => s.trim()).filter(Boolean);
      if (states.length === 0 || alphabet.length === 0) {
        alert('Please enter states and alphabet first.');
        return;
      }
      const syms = [...alphabet, 'eps'];
      const head = document.getElementById('nfaTransHead');
      const body = document.getElementById('nfaTransBody');
      head.innerHTML = ''; body.innerHTML = '';

      const hr = document.createElement('tr');
      const th0 = document.createElement('th'); th0.textContent = 'State'; hr.appendChild(th0);
      syms.forEach(sym => {
        const th = document.createElement('th');
        th.textContent = sym === 'eps' ? '\u03B5 (epsilon)' : '\u03B4(_, ' + sym + ')';
        hr.appendChild(th);
      });
      head.appendChild(hr);

      for (const st of states) {
        const row = document.createElement('tr');
        const tdState = document.createElement('td'); tdState.textContent = st; row.appendChild(tdState);
        syms.forEach(sym => {
          const td = document.createElement('td');
          const input = document.createElement('input');
          input.type = 'text'; input.id = 'nfa_' + st + '_' + sym;
          input.placeholder = '-';
          td.appendChild(input);
          row.appendChild(td);
        });
        body.appendChild(row);
      }
      document.getElementById('nfaTransTableWrap').style.display = '';
      document.getElementById('convertBtn').style.display = '';
    }

    parseNFA() {
      const states = document.getElementById('statesInput').value.split(',').map(s => s.trim()).filter(Boolean);
      const alphabet = document.getElementById('alphabetInput').value.split(',').map(s => s.trim()).filter(Boolean);
      const start = document.getElementById('startInput').value.trim();
      const accept = document.getElementById('acceptInput').value.split(',').map(s => s.trim()).filter(Boolean);
      if (states.length === 0 || alphabet.length === 0 || !start) { alert('Please fill in all NFA fields.'); return null; }
      if (!states.includes(start)) { alert('Start state must be one of the defined states.'); return null; }

      const transitions = [];
      const syms = [...alphabet, 'eps'];
      for (const st of states) {
        for (const sym of syms) {
          const input = document.getElementById('nfa_' + st + '_' + sym);
          if (!input) continue;
          const val = input.value.trim();
          if (!val || val === '-') continue;
          const targets = val.split(',').map(s => s.trim()).filter(Boolean);
          for (const t of targets) transitions.push({ from: st, symbol: sym, to: t });
        }
      }
      return new NFA(states, alphabet, transitions, start, accept);
    }

    startConversion() {
      const nfa = this.parseNFA();
      if (!nfa) return;
      this.nfa = nfa;
      this.steps = subsetConstruct(nfa);
      this.currentStep = 0;
      this.playing = false;

      document.getElementById('inputSection').style.display = 'none';
      document.getElementById('vizSection').style.display = '';

      // Init canvas graphs
      this.nfaGraph = new CanvasGraph('nfaCanvas');
      this.dfaGraph = new CanvasGraph('dfaCanvas');
      this.renderStep();
    }

    renderNFA(hlNfa) {
      const nfa = this.nfa;
      const positions = circularLayout(nfa.states, nfa.startState, GW, GH);
      this.nfaGraph.setData({
        states: nfa.states,
        transitions: nfa.transitions,
        startState: nfa.startState,
        acceptStates: nfa.acceptStates,
        positions: positions,
        isDFA: false,
        hlStates: hlNfa || new Set(),
        hlTrans: null
      });
    }

    renderStep() {
      const step = this.steps[this.currentStep];
      document.getElementById('stepCounter').textContent = (this.currentStep + 1) + ' / ' + this.steps.length;
      document.getElementById('prevBtn').disabled = this.currentStep === 0;
      document.getElementById('nextBtn').disabled = this.currentStep === this.steps.length - 1;

      // Show minimize button only at final step
      const isFinal = this.currentStep === this.steps.length - 1;
      document.getElementById('minimizeTrigger').style.display = isFinal ? '' : 'none';

      // Render the rich step explanation
      this._renderStepExplanation(step);

      // NFA
      this.renderNFA(step.hlNfa);

      // DFA
      const snap = step.snap;
      const dfaIds = snap.states.map(s => s.id);
      const dfaAccept = new Set(snap.states.filter(s => s.isAccept).map(s => s.id));
      const dfaStart = snap.states.length > 0 ? snap.states[0].id : null;
      const dfaPositions = polygonLayout(dfaIds, dfaStart, GW, GH);
      const hlDfa = new Set();
      if (step.current) hlDfa.add(step.current);

      this.dfaGraph.setData({
        states: dfaIds,
        transitions: snap.transitions,
        startState: dfaStart,
        acceptStates: dfaAccept,
        positions: dfaPositions,
        isDFA: true,
        stateData: snap.states,
        hlStates: hlDfa,
        hlTrans: step.hlTrans
      });

      renderDFATable(step.tableRows, this.nfa.alphabet);
    }

    _renderStepExplanation(step) {
      const container = document.getElementById('stepInfo');
      const ICONS = {
        info: '💡', algo: '⚙️', note: '📋', next: '➡️', formula: '📐',
        trace: '　↳', result: '✅', accept: '⭐', queue: '📦',
        state: '🔵', step: '📌', dead: '💀', new: '🆕', existing: '♻️',
        transition: '↗️', done: '🏁'
      };
      const TYPE_LABELS = {
        init: 'INITIALIZE', epsilon: 'ε-CLOSURE', process: 'PROCESSING',
        transition: 'TRANSITION', complete: 'COMPLETE'
      };
      const TYPE_COLORS = {
        init: 'var(--accent)', epsilon: 'var(--amber)',
        process: '#8B8BDA', transition: 'var(--green)', complete: 'var(--accent)'
      };

      let html = '';

      // Step badge + title
      const badgeColor = TYPE_COLORS[step.stepType] || 'var(--accent)';
      const badgeLabel = TYPE_LABELS[step.stepType] || '';
      html += '<div class="step-header">';
      html += '<span class="step-badge" style="background:' + badgeColor + '20;color:' + badgeColor + ';border:1px solid ' + badgeColor + '40">' + badgeLabel + '</span>';
      html += '<span class="step-number">Step ' + step.stepNumber + '</span>';
      html += '</div>';
      html += '<div class="step-title">' + step.title + '</div>';

      // Points
      if (step.points && step.points.length > 0) {
        html += '<div class="step-points">';
        for (const pt of step.points) {
          const icon = ICONS[pt.icon] || '•';
          const isSubStep = pt.icon === 'trace';
          const isSection = pt.icon === 'step';
          const isResult = pt.icon === 'result' || pt.icon === 'accept' || pt.icon === 'new' || pt.icon === 'existing' || pt.icon === 'dead' || pt.icon === 'transition' || pt.icon === 'done';
          let cls = 'step-point';
          if (isSubStep) cls += ' step-point-trace';
          if (isSection) cls += ' step-point-section';
          if (isResult) cls += ' step-point-result';
          html += '<div class="' + cls + '">';
          html += '<span class="step-icon">' + icon + '</span>';
          html += '<span class="step-text">' + this._highlightSyntax(pt.text) + '</span>';
          html += '</div>';
        }
        html += '</div>';
      }

      container.innerHTML = html;
    }

    _highlightSyntax(text) {
      // Highlight set notation {q0, q1} etc.
      let result = text.replace(/\{([^}]*)\}/g, '<span class="hl-set">{$1}</span>');
      // Highlight state references like D0, D1, q0, q1
      result = result.replace(/\b(D\d+)\b/g, '<span class="hl-dfa-state">$1</span>');
      // Highlight symbols after arrows
      result = result.replace(/—([a-zA-Z0-9])→/g, '—<span class="hl-symbol">$1</span>→');
      // Highlight ε
      result = result.replace(/ε/g, '<span class="hl-epsilon">ε</span>');
      // Highlight [NEW]
      result = result.replace(/\[NEW\]/g, '<span class="hl-new">[NEW]</span>');
      return result;
    }

    minimizeDFA() {
      // Get the final DFA from last step
      const finalSnap = this.steps[this.steps.length - 1].snap;
      const dfaIds = finalSnap.states.map(s => s.id);
      const dfaAccept = new Set(finalSnap.states.filter(s => s.isAccept).map(s => s.id));
      const dfaStart = finalSnap.states[0].id;
      const alphabet = this.nfa.alphabet;

      const minResult = minimizeDFAAlgorithm(dfaIds, finalSnap.transitions, dfaStart, dfaAccept, alphabet);

      // Show section
      document.getElementById('minSection').style.display = '';
      document.getElementById('minimizeTrigger').style.display = 'none';

      // Render original DFA graph (left)
      const origGraph = new CanvasGraph('dfaOrigCanvas');
      const origPositions = polygonLayout(dfaIds, dfaStart, GW, GH);
      origGraph.setData({
        states: dfaIds,
        transitions: finalSnap.transitions,
        startState: dfaStart,
        acceptStates: dfaAccept,
        positions: origPositions,
        isDFA: true,
        stateData: finalSnap.states,
        hlStates: new Set(),
        hlTrans: null
      });

      // Render minimized DFA graph (right)
      const minGraph = new CanvasGraph('dfaMinCanvas');
      const minIds = minResult.states.map(s => s.id);
      const minPositions = polygonLayout(minIds, minResult.startState, GW, GH);
      minGraph.setData({
        states: minIds,
        transitions: minResult.transitions,
        startState: minResult.startState,
        acceptStates: minResult.acceptStates,
        positions: minPositions,
        isDFA: true,
        stateData: minResult.states.map(s => ({
          id: s.id, nfaStates: new Set(s.origStates),
          isAccept: s.isAccept, isStart: s.isStart, isDead: false
        })),
        hlStates: new Set(),
        hlTrans: null
      });

      // Render minimized table
      renderMinTable(minResult, alphabet);

      // Scroll to minimization section
      document.getElementById('minSection').scrollIntoView({ behavior: 'smooth', block: 'start' });
    }

    next() {
      if (this.currentStep < this.steps.length - 1) { this.currentStep++; this.renderStep(); }
      if (this.currentStep === this.steps.length - 1 && this.playing) this.pause();
    }
    prev() { if (this.currentStep > 0) { this.currentStep--; this.renderStep(); } }
    togglePlay() { if (this.playing) this.pause(); else this.play(); }
    play() {
      this.playing = true;
      document.getElementById('playIcon').style.display = 'none';
      document.getElementById('pauseIcon').style.display = '';
      this.playTimer = setInterval(() => this.next(), 1800);
    }
    pause() {
      this.playing = false;
      document.getElementById('playIcon').style.display = '';
      document.getElementById('pauseIcon').style.display = 'none';
      clearInterval(this.playTimer);
    }
    reset() {
      this.pause();
      document.getElementById('vizSection').style.display = 'none';
      document.getElementById('inputSection').style.display = '';
      document.getElementById('minSection').style.display = 'none';
      document.getElementById('minimizeTrigger').style.display = 'none';
      // Restore the active mode panel
      if (this.inputMode === 'visual' && this.visualBuilder) {
        setTimeout(() => this.visualBuilder.resize(), 50);
      }
    }
  }

  window.app = new App();
  window.app.loadExample(0);
})();
