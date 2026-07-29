(function () {
  "use strict";
  const { GATES, CircuitEngine, PROOFS, QISKIT_RESULTS, helpers } = window.DagDemo;
  const $ = id => document.getElementById(id);
  const qiskit = new CircuitEngine("qiskit", 3);
  const isabelle = new CircuitEngine("isabelle", 3);
  let selectedGate = "H";
  let selectedNodeId = null;
  let selectedPanel = null;
  let trace = [];
  let step = 0;
  let zoom = 1;
  let pendingBase = null;

  const wireColors = ["#356ac3", "#d26042", "#22856c", "#9a5db1", "#b07a1b", "#287f9a", "#bf4f72", "#62753a"];

  function initialTrace() {
    const state = helpers.clone(isabelle.state);
    state.changedNodes = [];
    state.changedEdges = [];
    return [{
      qiskit: { state: helpers.clone(qiskit.state), title: "Create an empty DAGCircuit", explanation: "Each qubit wire starts at an input node and ends at an output node.", delta: ["input/output nodes", "one edge per qubit"] },
      isabelle: { state, title: "Create the empty graph", explanation: "Each qubit receives an input node, an output node, and a direct connecting edge. The frontier starts at the input, and the next available ID follows the boundary nodes.", delta: ["canonical boundary IDs", "frontier initialized", "next_id = 2n"] }
    }];
  }

  function combine(qTrace, iTrace) {
    const qiskitFocused = document.body.classList.contains("focus-qiskit");
    const primary = qiskitFocused ? qTrace : iTrace;
    const secondary = qiskitFocused ? iTrace : qTrace;
    const combined = [];
    for (let i = 0; i < primary.length; i += 1) {
      const secondaryIndex = primary.length === 1
        ? secondary.length - 1
        : Math.round(i * (secondary.length - 1) / (primary.length - 1));
      const primaryFrame = primary[i];
      const secondaryFrame = secondary[secondaryIndex];
      combined.push(qiskitFocused
        ? { qiskit: primaryFrame, isabelle: secondaryFrame }
        : { qiskit: secondaryFrame, isabelle: primaryFrame });
    }
    return combined;
  }

  function setTrace(next) {
    trace = next;
    step = 0;
    render();
  }

  function message(text, error = false) {
    $("message").textContent = text || "";
    $("message").classList.toggle("error", error);
  }

  function parseTargets() {
    const raw = $("qubitTargets").value.trim();
    if (!raw) return [];
    return raw.split(",").map(x => Number(x.trim()));
  }

  function currentPair() { return trace[step] || initialTrace()[0]; }

  function positions(state) {
    const ops = helpers.activeNodes(state).filter(n => n.type === "operation").sort((a, b) => a.id - b.id);
    const map = {};
    ops.forEach((n, i) => { map[n.id] = 205 + i * 100; });
    helpers.activeNodes(state).filter(n => n.type === "input").forEach(n => { map[n.id] = 115; });
    helpers.activeNodes(state).filter(n => n.type === "output").forEach(n => { map[n.id] = 215 + ops.length * 100; });
    return map;
  }

  function renderGraph(container, state, accent, soft, panelName, narration) {
    const pos = positions(state);
    const width = Math.max(620, 265 + helpers.activeNodes(state).filter(n => n.type === "operation").length * 92);
    const inner = document.createElement("div");
    inner.className = "graph-inner";
    inner.style.width = `${width}px`;
    inner.style.height = `${state.numQubits * 62 + 72}px`;
    inner.style.transform = `scale(${zoom})`;
    inner.style.setProperty("--panel-accent", accent);
    inner.style.setProperty("--panel-soft", soft);
    const callout = document.createElement("div");
    callout.className = "graph-callout";
    callout.dataset.step = step + 1;
    callout.textContent = narration;
    inner.appendChild(callout);
    for (let q = 0; q < state.numQubits; q += 1) {
      const row = document.createElement("div");
      row.className = "wire-row";
      row.style.setProperty("--wire-color", wireColors[q % wireColors.length]);
      row.innerHTML = `<span class="wire-label">q${q}</span><span class="wire-line"></span>`;
      state.edges.filter(e => e.wire === q).forEach(edge => {
        const segment = document.createElement("span");
        segment.className = "edge-segment";
        if ((state.changedEdges || []).includes(helpers.edgeKey(edge))) segment.classList.add("changed");
        const left = Math.min(pos[edge.source], pos[edge.target]);
        const right = Math.max(pos[edge.source], pos[edge.target]);
        segment.style.left = `${left}px`;
        segment.style.width = `${Math.max(1, right - left)}px`;
        segment.title = `${edge.source} → ${edge.target} on q${q}`;
        row.appendChild(segment);
      });
      (state.changedEdges || []).filter(key => !state.edges.some(e => helpers.edgeKey(e) === key)).forEach(key => {
        const match = key.match(/^(\d+)>(\d+)@(\d+)$/);
        if (!match || Number(match[3]) !== q) return;
        const marker = document.createElement("span");
        marker.className = "cut-marker";
        marker.style.left = `${(pos[Number(match[1])] + pos[Number(match[2])]) / 2 - 12}px`;
        marker.title = "This wire segment is removed in this step.";
        marker.textContent = "×";
        row.appendChild(marker);
      });
      inner.appendChild(row);
    }

    helpers.activeNodes(state).forEach(node => {
      node.qargs.forEach((q, index) => {
        const el = document.createElement(node.type === "operation" ? "button" : "span");
        el.className = `dag-node ${node.type}`;
        if (node.type === "operation" && index > 0) el.classList.add("satellite");
        if ((state.changedNodes || []).includes(node.id)) el.classList.add("changed");
        if (node.id === selectedNodeId) el.classList.add("selected");
        el.style.left = `${pos[node.id] - (node.type === "operation" ? 21 : 15)}px`;
        el.style.top = `${60 + q * 62 + (node.type === "operation" ? 10 : 16)}px`;
        el.style.setProperty("--panel-accent", accent);
        el.style.setProperty("--panel-soft", soft);
        const role = node.gate === "CNOT" ? (index === 0 ? "●" : "⊕")
          : node.gate === "CCNOT" ? (index < 2 ? "●" : "⊕")
          : (index === 0 ? node.gate : "•");
        el.innerHTML = `<span class="node-id">#${node.id}</span>${node.type === "operation" ? role : (node.type === "input" ? "IN" : "OUT")}`;
        const incident = state.edges.some(e => e.source === node.id || e.target === node.id);
        if (node.type === "operation" && !incident) el.classList.add("floating");
        el.title = node.type === "operation" ? `${node.gate} node ${node.id}, qargs [${node.qargs.join(", ")}]. Click to select.` : `${node.type} node ${node.id}`;
        if (node.type === "operation") {
          el.dataset.nodeId = node.id;
          el.dataset.panel = panelName;
          el.addEventListener("click", () => selectNode(node.id, panelName));
        }
        inner.appendChild(el);
      });
    });
    container.replaceChildren(inner);
  }

  function verticalPositions(state) {
    const nodes = helpers.activeNodes(state);
    const byId = new Map(nodes.map(node => [node.id, node]));
    const depth = Object.fromEntries(nodes.filter(node => node.type === "input").map(node => [node.id, 0]));
    const activeEdges = state.edges.filter(edge => byId.has(edge.source) && byId.has(edge.target));
    for (let pass = 0; pass < nodes.length; pass += 1) {
      activeEdges.forEach(edge => {
        if (depth[edge.source] == null || byId.get(edge.target).type === "output") return;
        depth[edge.target] = Math.max(depth[edge.target] ?? 0, depth[edge.source] + 1);
      });
    }
    nodes.filter(node => node.type === "operation" && depth[node.id] == null).forEach(node => {
      const predecessors = node.qargs.map(q => state.frontier[q]).filter(id => id !== node.id);
      depth[node.id] = Math.max(0, ...predecessors.map(id => depth[id] ?? 0)) + 1;
    });
    for (let pass = 0; pass < nodes.length; pass += 1) {
      activeEdges.forEach(edge => {
        if (depth[edge.source] == null || byId.get(edge.target).type === "output") return;
        depth[edge.target] = Math.max(depth[edge.target] ?? 0, depth[edge.source] + 1);
      });
    }
    const outputs = nodes.filter(node => node.type === "output");
    const operations = nodes.filter(node => node.type === "operation");
    const setOutputDepths = () => outputs.forEach(node => {
      const q = node.qargs[0];
      const incomingDepths = activeEdges
        .filter(edge => edge.target === node.id)
        .map(edge => depth[edge.source])
        .filter(value => value != null);
      depth[node.id] = Math.max(0, ...incomingDepths, depth[state.frontier[q]] ?? 0) + 1;
    });
    const preferredX = node => node.qargs.reduce((sum, q) => sum + 105 + q * 125, 0) / node.qargs.length;
    for (let pass = 0; pass < nodes.length * 2; pass += 1) {
      setOutputDepths();
      let moved = false;
      outputs.forEach(output => operations.forEach(operation => {
        if (depth[output.id] !== depth[operation.id]) return;
        if (Math.abs((105 + output.qargs[0] * 125) - preferredX(operation)) >= operationWidth(operation) / 2 + 26) return;
        depth[operation.id] += 1;
        moved = true;
      }));
      if (!moved) break;
      for (let propagation = 0; propagation < nodes.length; propagation += 1) {
        activeEdges.forEach(edge => {
          if (depth[edge.source] == null || byId.get(edge.target).type !== "operation") return;
          depth[edge.target] = Math.max(depth[edge.target] ?? 0, depth[edge.source] + 1);
        });
      }
    }
    setOutputDepths();
    const finalDepth = Math.max(1, ...Object.values(depth));
    return {
      y: Object.fromEntries(nodes.map(node => [node.id, 138 + depth[node.id] * 76])),
      depth,
      height: 138 + finalDepth * 76 + 100
    };
  }

  function qubitDescription(qargs) {
    if (qargs.length === 1) return `qubit ${qargs[0]}`;
    if (qargs.length === 2) return `qubits ${qargs[0]} (control) and ${qargs[1]} (target)`;
    return `qubits ${qargs[0]} and ${qargs[1]} (controls), and ${qargs[2]} (target)`;
  }

  function operationSummary(frame) {
    const operation = frame.state.currentOperation;
    if (!operation) return frame.state.action === "initial"
      ? `Create the empty ${frame.state.numQubits}-qubit graph`
      : frame.title;
    const location = qubitDescription(operation.qargs);
    let summary;
    if (operation.type === "insert") summary = `Insert ${operation.gate} gate at ${location}`;
    else if (operation.type === "delete") summary = `Delete ${operation.gate} gate at ${location}`;
    else if (operation.type === "replace") summary = `Replace ${operation.oldGate} with ${operation.gate} at ${location}`;
    else {
      const replacement = operation.replacement?.join(" → ");
      summary = `Replace ${operation.gate} at ${location} with ${replacement ? `${replacement} mini-DAG` : "a mini-DAG"}`;
    }
    return `${summary} — ${frame.title}`;
  }

  function operationWidth(node) {
    if (node.qargs.length === 3) return 200;
    if (node.qargs.length === 2) return 160;
    return 56;
  }

  function renderVerticalGraph(container, frame, accent, soft, panelName) {
    const state = frame.state;
    const layout = verticalPositions(state);
    const y = layout.y;
    const x = q => 105 + q * 125;
    const locatedWireMatch = frame.title.match(/Locate the end of wire q(\d+)/);
    const locatedWire = locatedWireMatch ? Number(locatedWireMatch[1]) : null;
    const insertionUnderConstruction = state.action === "insert"
      && helpers.activeNodes(state).some(node => node.type === "operation" && node.id === state.nextId);
    const constructionIds = new Set(
      insertionUnderConstruction
        ? helpers.activeNodes(state).filter(node => node.type === "operation" && node.id === state.nextId).map(node => node.id)
        : []
    );
    const constructionShift = 58;
    const activeOperations = helpers.activeNodes(state).filter(node => node.type === "operation");
    const operationX = {};
    const operationsByDepth = new Map();
    activeOperations.forEach(node => {
      const group = operationsByDepth.get(layout.depth[node.id]) || [];
      group.push(node);
      operationsByDepth.set(layout.depth[node.id], group);
    });
    operationsByDepth.forEach(nodes => {
      let right = 25;
      nodes
        .sort((a, b) => a.qargs.reduce((sum, q) => sum + x(q), 0) / a.qargs.length
          - b.qargs.reduce((sum, q) => sum + x(q), 0) / b.qargs.length)
        .forEach(node => {
          const width = operationWidth(node);
          const preferred = node.qargs.reduce((sum, q) => sum + x(q), 0) / node.qargs.length;
          const shift = constructionIds.has(node.id) ? constructionShift : 0;
          let center = Math.max(preferred + shift, right + 12 + width / 2);
          const outputCenters = helpers.activeNodes(state)
            .filter(output => output.type === "output" && layout.depth[output.id] === layout.depth[node.id])
            .map(output => x(output.qargs[0]));
          while (outputCenters.some(outputX => Math.abs(center - outputX) < width / 2 + 26)) {
            center = Math.max(...outputCenters.filter(outputX => Math.abs(center - outputX) < width / 2 + 26)) + width / 2 + 26;
          }
          operationX[node.id] = center - shift;
          right = center + width / 2;
        });
    });
    const graphWidth = Math.max(
      520,
      210 + state.numQubits * 125,
      ...activeOperations.map(node => operationX[node.id]
        + (constructionIds.has(node.id) ? constructionShift : 0)
        + operationWidth(node) / 2 + 60)
    );
    const inner = document.createElement("div");
    inner.className = "graph-inner vertical-graph";
    if (state.action === "insert" && !insertionUnderConstruction) inner.classList.add("insertion-complete");
    inner.style.width = `${graphWidth}px`;
    inner.style.height = `${Math.max(430, layout.height)}px`;
    inner.style.transform = `scale(${zoom})`;
    inner.style.setProperty("--panel-accent", accent);
    inner.style.setProperty("--panel-soft", soft);

    const callout = document.createElement("div");
    callout.className = "graph-callout";
    callout.dataset.step = step + 1;
    callout.textContent = operationSummary(frame);
    inner.appendChild(callout);

    const nodesById = new Map(helpers.activeNodes(state).map(node => [node.id, node]));
    const nodeX = (nodeId, wire) => {
      const node = nodesById.get(nodeId);
      const base = node?.type === "operation"
        ? operationX[nodeId]
        : x(wire);
      return base + (constructionIds.has(nodeId) ? constructionShift : 0);
    };
    const nodeY = nodeId => y[nodeId] + (nodesById.get(nodeId)?.type === "operation" ? 29 : 21);
    const addGraphEdge = (x1, y1, x2, y2, className, changed = false, located = false) => {
      const dx = x2 - x1;
      const dy = y2 - y1;
      const line = document.createElement("span");
      line.className = className;
      if (changed) line.classList.add("changed");
      if (located) line.classList.add("located-wire");
      line.style.left = `${x1}px`;
      line.style.top = `${y1}px`;
      line.style.width = `${Math.hypot(dx, dy)}px`;
      line.style.transform = `rotate(${Math.atan2(dy, dx)}rad)`;
      inner.appendChild(line);
    };

    for (let q = 0; q < state.numQubits; q += 1) {
      const label = document.createElement("span");
      label.className = "vertical-wire-label";
      label.style.left = `${x(q) - 14}px`;
      label.style.top = "108px";
      label.textContent = `q${q}`;
      inner.appendChild(label);

      state.edges.filter(e => e.wire === q).forEach(edge => {
        const constructingSource = constructionIds.has(edge.source);
        const constructingTarget = constructionIds.has(edge.target);
        addGraphEdge(
          nodeX(edge.source, q),
          nodeY(edge.source),
          nodeX(edge.target, q),
          nodeY(edge.target),
          locatedWire == null && (constructingSource || constructingTarget) ? "construction-edge" : "graph-edge",
          (state.changedEdges || []).includes(helpers.edgeKey(edge)),
          q === locatedWire && nodesById.get(edge.target)?.type === "output"
        );
      });

      (state.changedEdges || []).filter(key => !state.edges.some(e => helpers.edgeKey(e) === key)).forEach(key => {
        const match = key.match(/^(\d+)>(\d+)@(\d+)$/);
        if (!match || Number(match[3]) !== q) return;
        const source = Number(match[1]);
        const target = Number(match[2]);
        const marker = document.createElement("span");
        marker.className = "cut-marker vertical-cut";
        marker.style.left = `${(nodeX(source, q) + nodeX(target, q)) / 2 - 14}px`;
        marker.style.top = `${(nodeY(source) + nodeY(target)) / 2 - 14}px`;
        marker.textContent = "×";
        marker.title = "This edge is removed in this step.";
        inner.appendChild(marker);
      });
    }

    helpers.activeNodes(state).forEach(node => {
      [node.qargs[0]].forEach(q => {
        const operation = node.type === "operation";
        const multi = operation && node.qargs.length > 1;
        const width = operation ? operationWidth(node) : 40;
        const el = document.createElement(operation ? "button" : "span");
        el.className = `dag-node ${node.type}`;
        if (multi) el.classList.add("multi-operation");
        if ((state.changedNodes || []).includes(node.id)) el.classList.add("changed");
        if (state.action === "delete" && state.deletingNodeId === node.id && step >= 2) el.classList.add("deleting");
      if (node.id === selectedNodeId) el.classList.add("selected");
      el.style.left = `${nodeX(node.id, q) - width / 2}px`;
      el.style.top = `${y[node.id]}px`;
      el.style.width = `${width}px`;
        el.style.setProperty("--panel-accent", accent);
        el.style.setProperty("--panel-soft", soft);
        const roles = node.gate === "CNOT"
          ? `q${node.qargs[0]} control → q${node.qargs[1]} target`
          : node.gate === "CCNOT"
            ? `q${node.qargs[0]}, q${node.qargs[1]} controls → q${node.qargs[2]} target`
            : "";
        el.innerHTML = operation
          ? `<span class="gate-name">${node.gate}</span>${roles ? `<span class="gate-roles">${roles}</span>` : ""}<span class="node-id">#${node.id}</span>`
          : `<span class="node-id">#${node.id}</span>${node.type === "input" ? "IN" : "OUT"}`;
        if (locatedWire == null && constructionIds.has(node.id)) el.classList.add("constructing");
        if (operation) {
          el.dataset.nodeId = node.id;
          el.dataset.panel = panelName;
          el.title = `${node.gate} node ${node.id}, ordered qubits [${node.qargs.join(", ")}]. Click after the current operation is complete.`;
          el.addEventListener("click", () => selectNode(node.id, panelName));
        }
        inner.appendChild(el);
      });
    });
    container.replaceChildren(inner);
  }

  function nodeTableLegacy(container, state, narration) {
    const rows = state.nodes.slice().sort((a, b) => a.id - b.id).map(n => {
      const changed = (state.changedNodes || []).includes(n.id) ? "changed" : "";
      const value = n.active === false ? (state.kind === "isabelle" ? "None" : "removed") : n.type === "operation" ? `OperationNode ${n.gate}` : `${n.type === "input" ? "InputNode" : "OutputNode"} q${n.qargs[0]}`;
      const qargs = n.gate === "CNOT"
        ? `[q${n.qargs[0]} control, q${n.qargs[1]} target]`
        : n.gate === "CCNOT"
          ? `[q${n.qargs[0]} control, q${n.qargs[1]} control, q${n.qargs[2]} target]`
          : `[${n.qargs.map(q => `q${q}`).join(", ")}]`;
      return `<tr class="${changed}"><td>${n.id}</td><td>${value}</td><td>${n.active === false ? "—" : qargs}</td></tr>`;
    }).join("");
    container.innerHTML = `<table><thead><tr><th>ID</th><th>stored value</th><th>qargs / roles</th></tr></thead><tbody>${rows}</tbody></table>`;
  }

  function nodeTable(container, state) {
    const change = state.tableChange;
    const changedIds = new Set(change ? change.nodeIds : []);
    const rows = state.nodes.slice().sort((a, b) => a.id - b.id).map(n => {
        const value = n.active === false
          ? (state.kind === "isabelle" ? "None" : "removed")
          : n.type === "operation" ? `${state.kind === "qiskit" ? "DAGOpNode" : "OperationNode"} ${n.gate}`
          : `${n.type === "input" ? "InputNode" : "OutputNode"} q${n.qargs[0]}`;
        const qargs = n.gate === "CNOT"
          ? `[q${n.qargs[0]} control, q${n.qargs[1]} target]`
          : n.gate === "CCNOT"
            ? `[q${n.qargs[0]} control, q${n.qargs[1]} control, q${n.qargs[2]} target]`
            : `[${n.qargs.map(q => `q${q}`).join(", ")}]`;
        const changed = changedIds.has(n.id) ? `table-change ${change.kind}` : "";
        return `<tr class="${changed}"><td>${n.id}</td><td>${value}</td><td>${n.active === false ? "—" : qargs}</td></tr>`;
      }).join("");
    container.innerHTML = `<table><thead><tr><th>ID</th><th>stored value</th><th>qargs / roles</th></tr></thead><tbody>${rows}</tbody></table>`;
  }

  function frontierTable(container, state, isQiskit, previousState) {
    const rows = Array.from({ length: state.numQubits }, (_, q) => {
      const changed = previousState && previousState.frontier[q] !== state.frontier[q];
      const meaning = isQiskit ? "<td>output predecessor</td>" : "";
      return `<tr class="${changed ? "frontier-change" : ""}"><td>q${q}</td><td>${state.frontier[q]}</td>${meaning}</tr>`;
    }).join("");
    const meaningHeading = isQiskit ? "<th>meaning</th>" : "";
    container.innerHTML = `<table><thead><tr><th>wire</th><th>node ID</th>${meaningHeading}</tr></thead><tbody>${rows}</tbody></table>`;
  }

  function render() {
    const pair = currentPair();
    const qs = pair.qiskit.state;
    const is = pair.isabelle.state;
    const previousPair = step > 0 ? trace[step - 1] : null;
    const previousQiskit = previousPair ? previousPair.qiskit.state : pendingBase?.qiskit;
    const previousIsabelle = previousPair ? previousPair.isabelle.state : pendingBase?.isabelle;
    renderVerticalGraph($("qiskitGraph"), pair.qiskit, "#5a39b8", "#eeeafd", "qiskit");
    renderVerticalGraph($("isabelleGraph"), pair.isabelle, "#087b72", "#e5f5f2", "isabelle");
    nodeTable($("qiskitNodes"), qs);
    nodeTable($("isabelleNodes"), is);
    frontierTable($("qiskitFrontier"), qs, true, previousQiskit);
    frontierTable($("isabelleFrontier"), is, false, previousIsabelle);
    $("recordQubits").textContent = is.numQubits;
    $("recordNodes").textContent = `${helpers.activeNodes(is).length} active`;
    $("recordEdges").textContent = is.edges.length;
    $("recordNext").textContent = is.nextId;
    $("stepCounter").textContent = `Step ${step + 1} of ${trace.length}`;
    $("goToStepInput").max = trace.length;
    $("goToStepInput").value = step + 1;
    const focused = document.body.classList.contains("focus-qiskit") ? pair.qiskit
      : document.body.classList.contains("focus-isabelle") ? pair.isabelle : pair.isabelle;
    $("stepTitle").textContent = focused.title;
    $("stepExplanation").textContent = focused.explanation;
    const deltas = [...new Set(focused.delta || [])];
    $("deltaList").innerHTML = deltas.map(d => `<span>${escapeHtml(d)}</span>`).join("");
    const qiskitFocused = document.body.classList.contains("focus-qiskit");
    const action = focused.state.action || "initial";
    const result = qiskitFocused ? QISKIT_RESULTS[action] || QISKIT_RESULTS.initial : PROOFS[action] || PROOFS.initial;
    $("proofEyebrow").textContent = qiskitFocused ? "Result of this Qiskit operation" : "What has been established?";
    $("proofTitle").textContent = result.title;
    $("proofList").innerHTML = result.bullets.map(b => `<li>${escapeHtml(b)}</li>`).join("");
    $("theoremDetails").hidden = qiskitFocused;
    $("theoremNames").innerHTML = qiskitFocused ? "" : result.names.map(n => `<code>${n}</code>`).join("");
    $("prevStep").disabled = step <= 0;
    $("firstStep").disabled = step <= 0;
    $("nextStep").disabled = step >= trace.length - 1;
    $("lastStep").disabled = step >= trace.length - 1;
    const pending = Boolean(pendingBase) && step < trace.length - 1;
    $("cancelOperation").disabled = !pending;
    $("controlDeck").classList.toggle("operation-pending", pending);
    document.querySelectorAll("#gatePalette button, #qubitTargets, #insertBtn, #deleteBtn, #replaceBtn, #substituteBtn, #initializeBtn, #presetSelect").forEach(control => {
      control.disabled = pending || ((control.id === "deleteBtn" || control.id === "replaceBtn" || control.id === "substituteBtn") && selectedNodeId == null);
    });
  }

  function escapeHtml(value) {
    return String(value).replace(/[&<>"']/g, c => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#039;" }[c]));
  }

  function selectNode(id, panel) {
    if (pendingBase && step < trace.length - 1) {
      message("Finish the current operation with Next step, or cancel it. This node is not selectable yet.", true);
      return;
    }
    selectedNodeId = id;
    selectedPanel = panel;
    $("deleteBtn").disabled = false;
    $("replaceBtn").disabled = false;
    $("substituteBtn").disabled = false;
    message(`Selected operation node ${id}. Choose Delete, Replace, or Replace with mini-DAG.`);
    render();
  }

  function initialize(n = Number($("qubitCount").value)) {
    if (!Number.isInteger(n) || n < 1 || n > 4) return message("Choose a whole number from 1 to 4.", true);
    qiskit.initialize(n);
    isabelle.initialize(n);
    selectedNodeId = null;
    selectedPanel = null;
    pendingBase = null;
    $("qubitCount").value = n;
    $("deleteBtn").disabled = $("replaceBtn").disabled = $("substituteBtn").disabled = true;
    message("");
    setTrace(initialTrace());
  }

  function runBoth(method, ...args) {
    const qBefore = helpers.clone(qiskit.state);
    const iBefore = helpers.clone(isabelle.state);
    try {
      pendingBase = { qiskit: qBefore, isabelle: iBefore };
      let qResult;
      let iResult;
      qResult = qiskit[method](...args);
      iResult = isabelle[method](...args);
      selectedNodeId = null;
      $("deleteBtn").disabled = $("replaceBtn").disabled = $("substituteBtn").disabled = true;
      setTrace(combine(qResult.trace, iResult.trace));
      message("");
      return { qResult, iResult };
    } catch (error) {
      qiskit.load(qBefore);
      isabelle.load(iBefore);
      pendingBase = null;
      message(error.message, true);
      return null;
    }
  }

  function insert() { runBoth("insert", selectedGate, parseTargets()); }
  function remove() { if (selectedNodeId != null) runBoth("delete", selectedNodeId); }
  function selectedOperation() {
    return selectedNodeId == null ? null : helpers.opAt(isabelle.state, selectedNodeId);
  }

  function openGateReplacementBuilder() {
    const target = selectedOperation();
    if (!target) return;
    const compatible = Object.entries(GATES)
      .filter(([, definition]) => definition.arity === target.qargs.length)
      .map(([name]) => name);
    $("replaceGateSelect").innerHTML = compatible
      .map(name => `<option value="${name}" ${name === target.gate ? "selected" : ""}>${name}</option>`)
      .join("");
    $("replaceGateTarget").textContent = `Node ${target.id} currently contains ${target.gate} on [${target.qargs.map(q => `q${q}`).join(", ")}]. Only gates with the same width are available.`;
    $("replaceGateError").textContent = "";
    $("gateReplacementDialog").showModal();
  }

  function confirmGateReplacement() {
    const result = runBoth("replaceGate", selectedNodeId, $("replaceGateSelect").value);
    if (result) $("gateReplacementDialog").close();
    else $("replaceGateError").textContent = $("message").textContent;
  }

  function addMiniDagRow(gate = "H", qargs = []) {
    const row = document.createElement("div");
    row.className = "mini-dag-row";
    const options = Object.keys(GATES).map(name => `<option value="${name}" ${name === gate ? "selected" : ""}>${name}</option>`).join("");
    row.innerHTML = `<select aria-label="Replacement gate">${options}</select><input type="text" aria-label="Ordered host qubits" value="${qargs.join(", ")}" placeholder="e.g. 0, 1"><button type="button" class="remove-builder-row quiet" aria-label="Remove this operation">×</button>`;
    row.querySelector(".remove-builder-row").addEventListener("click", () => {
      if ($("miniDagRows").children.length > 1) row.remove();
    });
    $("miniDagRows").appendChild(row);
  }

  function openMiniDagBuilder() {
    const target = selectedOperation();
    if (!target) return;
    $("miniDagRows").replaceChildren();
    $("miniDagError").textContent = "";
    $("miniDagInterface").textContent = `Replace node ${target.id} (${target.gate}) using host interface [${target.qargs.map(q => `q${q}`).join(", ")}]. Operations run from top to bottom in the order below.`;
    addMiniDagRow("H", [target.qargs[0]]);
    addMiniDagRow(target.gate, target.qargs);
    $("miniDagDialog").showModal();
  }

  function readMiniDagBuilder() {
    return [...$("miniDagRows").querySelectorAll(".mini-dag-row")].map(row => ({
      gate: row.querySelector("select").value,
      qargs: row.querySelector("input").value
        .split(",")
        .map(value => value.trim())
        .filter(Boolean)
        .map(Number)
    }));
  }

  function confirmMiniDagBuilder() {
    const result = runBoth("replaceWithSubcircuit", selectedNodeId, readMiniDagBuilder());
    if (result) $("miniDagDialog").close();
    else $("miniDagError").textContent = $("message").textContent;
  }

  function cancelPendingOperation() {
    if (!pendingBase || step >= trace.length - 1) return;
    qiskit.load(pendingBase.qiskit);
    isabelle.load(pendingBase.isabelle);
    pendingBase = null;
    selectedNodeId = null;
    const qState = helpers.clone(qiskit.state);
    const iState = helpers.clone(isabelle.state);
    qState.changedNodes = []; qState.changedEdges = [];
    iState.changedNodes = []; iState.changedEdges = [];
    trace = [{
      qiskit: { state: qState, title: "Operation cancelled", explanation: "The complete pending transformation was discarded; the DAG is exactly as it was before it began.", delta: ["state restored"] },
      isabelle: { state: iState, title: "Operation cancelled", explanation: "The complete pending transformation was discarded; the circuit and frontier are restored together.", delta: ["state restored"] }
    }];
    step = 0;
    message("Operation cancelled. No partial node, edge, or table update was kept.");
    render();
  }

  function goToStep(requestedStep) {
    if (!trace.length || !Number.isFinite(requestedStep)) return;
    step = Math.max(0, Math.min(trace.length - 1, Math.trunc(requestedStep)));
    render();
  }

  function goToEnteredStep() {
    const requestedStep = Number($("goToStepInput").value);
    if (!Number.isInteger(requestedStep) || requestedStep < 1 || requestedStep > trace.length) {
      message(`Enter a step from 1 to ${trace.length}.`, true);
      return;
    }
    message("");
    goToStep(requestedStep - 1);
  }

  function selectGate(gate) {
    selectedGate = gate;
    document.querySelectorAll(".gate").forEach(b => b.classList.toggle("active", b.dataset.gate === gate));
    const ordering = gate === "CNOT" ? " Enter control first, target second."
      : gate === "CCNOT" ? " Enter control 1, control 2, then target." : "";
    $("gateHint").textContent = `${gate} needs ${GATES[gate].arity} distinct qubit${GATES[gate].arity === 1 ? "" : "s"}.${ordering}`;
  }

  function buildPalette() {
    Object.keys(GATES).forEach(gate => {
      const button = document.createElement("button");
      button.className = "gate";
      button.dataset.gate = gate;
      button.textContent = gate;
      button.draggable = true;
      button.title = `Select ${gate}; ${GATES[gate].arity}-qubit gate`;
      button.addEventListener("click", () => selectGate(gate));
      button.addEventListener("dragstart", e => e.dataTransfer.setData("text/plain", gate));
      $("gatePalette").appendChild(button);
    });
    selectGate("H");
  }

  function preset(name) {
    if (name === "qasm") {
      initialize(4);
      pendingBase = {
        qiskit: helpers.clone(qiskit.state),
        isabelle: helpers.clone(isabelle.state)
      };
      const operations = [
        ["S", [0]], ["Y", [1]], ["S", [2]], ["Z", [3]],
        ["CNOT", [2, 3]], ["X", [0]], ["X", [1]], ["Z", [2]], ["T", [3]],
        ["CNOT", [0, 2]], ["X", [0]], ["T", [1]], ["T", [2]], ["Y", [3]],
        ["CNOT", [2, 0]], ["Z", [0]], ["Z", [1]], ["S", [2]], ["T", [3]],
        ["CNOT", [1, 0]]
      ];
      const walkthrough = [];
      operations.forEach(([gate, qargs]) => {
        const qResult = qiskit.insert(gate, qargs);
        const iResult = isabelle.insert(gate, qargs);
        walkthrough.push(...combine(qResult.trace, iResult.trace));
      });
      selectedNodeId = null;
      selectedPanel = null;
      $("deleteBtn").disabled = $("replaceBtn").disabled = $("substituteBtn").disabled = true;
      trace = walkthrough;
      step = 0;
      message("QASM walkthrough ready. Press Next to build all 20 operations; measurements are omitted.");
      return render();
    }
    initialize(3);
    if (name === "single") { selectGate("H"); $("qubitTargets").value = "0"; return insert(); }
    if (name === "multi") {
      runBoth("insert", "CNOT", [0, 1]);
      return runBoth("insert", "CCNOT", [0, 1, 2]);
    }
    if (name === "delete") {
      runBoth("insert", "H", [0]);
      const middle = runBoth("insert", "X", [0]);
      runBoth("insert", "Z", [0]);
      return runBoth("delete", middle.iResult.nodeId);
    }
    if (name === "replace") {
      const added = runBoth("insert", "H", [1]);
      selectGate("X");
      return runBoth("replaceGate", added.iResult.nodeId, "X");
    }
    if (name === "subdag") {
      const added = runBoth("insert", "CNOT", [0, 1]);
      return runBoth("replaceWithSubcircuit", added.iResult.nodeId, [
        { gate: "H", qargs: [0] },
        { gate: "CNOT", qargs: [0, 1] }
      ]);
    }
  }

  function exportScenario() {
    const payload = { format: "dag-visual-demo", version: 1, qiskit: qiskit.state, isabelle: isabelle.state };
    const blob = new Blob([JSON.stringify(payload, null, 2)], { type: "application/json" });
    const link = document.createElement("a");
    link.href = URL.createObjectURL(blob);
    link.download = "dag-scenario.json";
    link.click();
    URL.revokeObjectURL(link.href);
  }

  async function importScenario(file) {
    try {
      const payload = JSON.parse(await file.text());
      if (payload.format !== "dag-visual-demo" || !payload.qiskit || !payload.isabelle) throw new Error("This is not a DAG demonstrator scenario file.");
      if (!Number.isInteger(payload.isabelle.numQubits) || payload.isabelle.numQubits < 1 || payload.isabelle.numQubits > 4) throw new Error("Imported scenarios must contain 1–4 qubits.");
      qiskit.load(payload.qiskit);
      isabelle.load(payload.isabelle);
      $("qubitCount").value = isabelle.state.numQubits;
      setTrace(initialTrace().map(pair => ({ qiskit: { ...pair.qiskit, state: helpers.clone(qiskit.state) }, isabelle: { ...pair.isabelle, state: helpers.clone(isabelle.state) } })));
      message("Scenario imported.");
    } catch (error) { message(error.message, true); }
  }

  function bind() {
    $("initializeBtn").addEventListener("click", () => initialize());
    $("insertBtn").addEventListener("click", insert);
    $("deleteBtn").addEventListener("click", remove);
    $("replaceBtn").addEventListener("click", openGateReplacementBuilder);
    $("confirmGateReplacement").addEventListener("click", confirmGateReplacement);
    $("substituteBtn").addEventListener("click", openMiniDagBuilder);
    $("addMiniDagRow").addEventListener("click", () => {
      const target = selectedOperation();
      addMiniDagRow("H", target ? [target.qargs[0]] : [0]);
    });
    $("confirmMiniDag").addEventListener("click", confirmMiniDagBuilder);
    $("prevStep").addEventListener("click", () => goToStep(step - 1));
    $("nextStep").addEventListener("click", () => goToStep(step + 1));
    $("firstStep").addEventListener("click", () => goToStep(0));
    $("lastStep").addEventListener("click", () => goToStep(trace.length - 1));
    $("goToStepButton").addEventListener("click", goToEnteredStep);
    $("goToStepInput").addEventListener("keydown", event => {
      if (event.key === "Enter") goToEnteredStep();
    });
    $("cancelOperation").addEventListener("click", cancelPendingOperation);
    $("zoomRange").addEventListener("input", e => { zoom = Number(e.target.value) / 100; render(); });
    $("qubitCount").addEventListener("change", e => {
      const value = Number(e.target.value);
      if (!Number.isFinite(value)) e.target.value = 1;
      else e.target.value = Math.min(4, Math.max(1, Math.round(value)));
    });
    $("presetSelect").addEventListener("change", e => { if (e.target.value) preset(e.target.value); e.target.value = ""; });
    $("exportBtn").addEventListener("click", exportScenario);
    $("importInput").addEventListener("change", e => { if (e.target.files[0]) importScenario(e.target.files[0]); e.target.value = ""; });
    $("sourcesBtn").addEventListener("click", () => $("sourcesDialog").showModal());
    const focus = implementation => {
      initialize(3);
      selectGate("H");
      $("qubitTargets").value = "0";
      zoom = 1;
      $("zoomRange").value = "100";
      document.body.classList.toggle("focus-qiskit", implementation === "qiskit");
      document.body.classList.toggle("focus-isabelle", implementation === "isabelle");
      const panel = document.querySelector(`.${implementation}-panel`);
      panel.querySelector(".panel-heading").after($("controlDeck"), $("playbackBar"));
      message(`${implementation === "qiskit" ? "Qiskit" : "Isabelle"} explainer open. Prepare an operation, then press Next step.`);
      render();
    };
    $("focusQiskit").addEventListener("click", () => focus("qiskit"));
    $("focusIsabelle").addEventListener("click", () => focus("isabelle"));
    document.querySelectorAll(".close-focus").forEach(button => button.addEventListener("click", () => {
      if (pendingBase && step < trace.length - 1) cancelPendingOperation();
      pendingBase = null;
      const picker = document.querySelector(".stage-picker");
      picker.before($("controlDeck"));
      picker.after($("playbackBar"));
      document.body.classList.remove("focus-qiskit", "focus-isabelle");
      message("");
    }));
    $("fullscreenBtn").addEventListener("click", async () => {
      document.body.classList.toggle("presentation");
      try {
        if (!document.fullscreenElement) await document.documentElement.requestFullscreen();
        else await document.exitFullscreen();
      } catch (_) { /* file browsers may decline fullscreen; compact presentation mode still works */ }
    });
    document.addEventListener("keydown", e => {
      if (e.target.matches("input, select")) return;
      if (e.key === "ArrowRight") goToStep(step + 1);
      if (e.key === "ArrowLeft") goToStep(step - 1);
    });
    ["qiskitGraph", "isabelleGraph"].forEach(id => {
      $(id).addEventListener("dragover", e => e.preventDefault());
      $(id).addEventListener("drop", e => {
        e.preventDefault();
        const gate = e.dataTransfer.getData("text/plain");
        if (GATES[gate]) { selectGate(gate); message(`${gate} selected. Enter its ordered qubits, then choose Insert at back.`); }
      });
    });
  }

  buildPalette();
  bind();
  trace = initialTrace();
  render();
}());
