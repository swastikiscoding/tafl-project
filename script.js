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

    steps.push({ desc: 'Starting subset construction. The original NFA is shown on the left.', detail: 'We begin by computing the epsilon-closure of the NFA start state.', snap: snap(), current: null, symbol: null, hlNfa: new Set(), hlTrans: null, tableRows: [] });

    const startClosure = nfa.epsilonClosure(new Set([nfa.startState]));
    const startRes = getOrCreate(startClosure);
    steps.push({
      desc: 'eps-closure({' + nfa.startState + '}) = ' + setStr(startClosure),
      detail: 'This becomes DFA state ' + startRes.id + (dfaStates[0].isAccept ? ' (accepting).' : '.'),
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
      for (const sym of nfa.alphabet) {
        const moveRes = nfa.move(ds.nfaStates, sym);
        const closure = nfa.epsilonClosure(moveRes);
        const res = getOrCreate(closure);
        if (res.isNew) queue.push(dfaStates.length - 1);
        dfaTransitions.push({ from: ds.id, to: res.id, symbol: sym });
        const target = dfaStates.find(s => s.id === res.id);
        steps.push({
          desc: 'delta(' + ds.id + ', ' + sym + '): move(' + setStr(ds.nfaStates) + ', ' + sym + ') = ' + setStr(moveRes),
          detail: 'eps-closure(' + setStr(moveRes) + ') = ' + setStr(closure) + ' = ' + res.id +
            (res.isNew ? ' [NEW]' : '') + (target.isDead ? ' (dead state)' : '') + (target.isAccept ? ' (accepting)' : ''),
          snap: snap(), current: ds.id, symbol: sym, hlNfa: new Set(closure),
          hlTrans: { from: ds.id, to: res.id },
          tableRows: buildTable(dfaStates, dfaTransitions, nfa.alphabet, ds.id, sym)
        });
      }
    }
    steps.push({
      desc: 'Subset construction complete.',
      detail: 'The DFA has ' + dfaStates.length + ' states and ' + dfaTransitions.length + ' transitions.',
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
      document.getElementById('stepDescription').textContent = step.desc;
      document.getElementById('stepDetail').textContent = step.detail || '';
      document.getElementById('stepCounter').textContent = (this.currentStep + 1) + ' / ' + this.steps.length;
      document.getElementById('prevBtn').disabled = this.currentStep === 0;
      document.getElementById('nextBtn').disabled = this.currentStep === this.steps.length - 1;

      // Show minimize button only at final step
      const isFinal = this.currentStep === this.steps.length - 1;
      document.getElementById('minimizeTrigger').style.display = isFinal ? '' : 'none';

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
    }
  }

  window.app = new App();
  window.app.loadExample(0);
})();
