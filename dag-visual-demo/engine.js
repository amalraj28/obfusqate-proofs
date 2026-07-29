(function (global) {
  "use strict";

  const GATES = {
    H: { arity: 1 }, X: { arity: 1 }, Y: { arity: 1 }, Z: { arity: 1 },
    S: { arity: 1 }, T: { arity: 1 }, RZ: { arity: 1 },
    CNOT: { arity: 2 }, CCNOT: { arity: 3 }
  };

  const clone = value => JSON.parse(JSON.stringify(value));
  const edgeKey = e => `${e.source}>${e.target}@${e.wire}`;
  const activeNodes = state => state.nodes.filter(n => n.active !== false);
  const nodeAt = (state, id) => state.nodes.find(n => n.id === id && n.active !== false);
  const opAt = (state, id) => {
    const node = nodeAt(state, id);
    return node && node.type === "operation" ? node : null;
  };

  function makeInitial(kind, n) {
    const nodes = [];
    const edges = [];
    const frontier = {};
    for (let q = 0; q < n; q += 1) {
      const input = kind === "isabelle" ? 2 * q : q;
      const output = kind === "isabelle" ? 2 * q + 1 : n + q;
      nodes.push({ id: input, type: "input", qargs: [q], label: `in${q}`, active: true });
      nodes.push({ id: output, type: "output", qargs: [q], label: `out${q}`, active: true });
      edges.push({ source: input, target: output, wire: q });
      frontier[q] = input;
    }
    return { kind, numQubits: n, nodes, edges, frontier, nextId: 2 * n, action: "initial" };
  }

  function validateOperation(state, gate, qargs) {
    if (!GATES[gate]) throw new Error(`Unknown gate ${gate}.`);
    if (qargs.length !== GATES[gate].arity) throw new Error(`${gate} requires ${GATES[gate].arity} qubit${GATES[gate].arity === 1 ? "" : "s"}.`);
    if (new Set(qargs).size !== qargs.length) throw new Error("Qubit arguments must be distinct.");
    if (qargs.some(q => !Number.isInteger(q) || q < 0 || q >= state.numQubits)) throw new Error(`Qubits must be between 0 and ${state.numQubits - 1}.`);
  }

  function outputId(state, q) {
    return state.kind === "isabelle" ? 2 * q + 1 : state.numQubits + q;
  }

  function predecessorOf(state, target, wire) {
    const edge = state.edges.find(e => e.target === target && e.wire === wire);
    return edge ? edge.source : null;
  }

  function successorOf(state, source, wire) {
    const edge = state.edges.find(e => e.source === source && e.wire === wire);
    return edge ? edge.target : null;
  }

  function addStep(trace, state, title, explanation, delta, changedNodes = [], changedEdges = [], tableChange = null) {
    const snapshot = clone(state);
    snapshot.changedNodes = changedNodes;
    snapshot.changedEdges = changedEdges;
    snapshot.tableChange = tableChange;
    trace.push({ state: snapshot, title, explanation, delta });
  }

  function insertTraceLegacy(start, gate, qargs) {
    validateOperation(start, gate, qargs);
    const s = clone(start);
    s.action = "insert";
    s.currentOperation = { type: "insert", gate, qargs: clone(qargs) };
    const trace = [];
    const roles = gate === "CNOT"
      ? `q${qargs[0]} is the control and q${qargs[1]} is the target.`
      : gate === "CCNOT"
        ? `q${qargs[0]} and q${qargs[1]} are controls; q${qargs[2]} is the target.`
        : "";
    addStep(trace, s, `Validate ${gate}(${qargs.map(q => `q${q}`).join(", ")})`,
      s.kind === "qiskit"
        ? `The gate width must match the ordered qubit list, and every selected qubit must belong to this graph. ${roles}`
        : `The gate must receive the correct number of distinct qubits, all of which must belong to this circuit. ${roles}`,
      [`gate arity = ${qargs.length}`, "qargs valid", roles].filter(Boolean));

    const id = s.nextId;
    if (s.kind === "isabelle") {
      addStep(trace, s, `Read next_id = ${id}`, "The fresh global node ID is read before any graph field is changed.", [`new_node_id = ${id}`], [id]);
    }
    s.nodes.push({ id, type: "operation", gate, qargs: clone(qargs), label: gate, active: true });
    addStep(trace, s, `Allocate operation node ${id}`, s.kind === "qiskit"
      ? "A DAGOpNode stores the operation and its ordered qargs."
      : "The node table stores the new operation at the next available ID.",
      [`nodes[${id}] = ${gate}`, `qargs = [${qargs.join(", ")}]`], [id], [],
      { kind: "add", nodeIds: [id], description: `Add node ${id} containing ${gate}.` });

    for (const q of qargs) {
      const out = outputId(s, q);
      const predecessor = predecessorOf(s, out, q);
      addStep(trace, s, `Locate the end of wire q${q}`, s.kind === "qiskit"
        ? `The predecessor immediately before q${q}'s output is node ${predecessor}.`
        : `frontier(q${q}) is node ${s.frontier[q]}; the final edge currently goes from it to output ${out}.`,
        [`predecessor = ${predecessor}`, `output = ${out}`], [predecessor, out]);

      const removed = { source: predecessor, target: out, wire: q };
      s.edges = s.edges.filter(e => edgeKey(e) !== edgeKey(removed));
      addStep(trace, s, `Remove the old q${q} edge`, `The direct edge ${predecessor} → ${out} is removed before the wire is spliced through the new node.`, [`− ${edgeKey(removed)}`], [id], [edgeKey(removed)]);

      const left = { source: predecessor, target: id, wire: q };
      const right = { source: id, target: out, wire: q };
      s.edges.push(left, right);
      addStep(trace, s, `Splice node ${id} into q${q}`, `Two wire-labelled edges replace the old one: predecessor → operation → output.`, [`+ ${edgeKey(left)}`, `+ ${edgeKey(right)}`], [id], [edgeKey(left), edgeKey(right)]);
      s.frontier[q] = id;
      addStep(trace, s, s.kind === "qiskit" ? `Refresh q${q}'s end-point view` : `Update frontier(q${q})`,
        s.kind === "qiskit"
          ? "The teaching table is recomputed from the output predecessor. It is not a public Qiskit frontier record."
          : `The frontier entry for q${q} now points to node ${id}; all other entries stay unchanged.`,
        [`q${q} ↦ ${id}`], [id]);
    }
    s.nextId += 1;
    addStep(trace, s, s.kind === "qiskit" ? "Append is complete" : `Insertion is complete — advance next_id to ${s.nextId}`,
      s.kind === "qiskit"
        ? "The new operation is now the final operation on every affected quantum wire."
        : "The next available ID moves forward, so deleted IDs will not be reused.",
      [`next_id = ${s.nextId}`, `${gate} inserted`], [id]);
    return { trace, final: clone(s), nodeId: id };
  }

  function insertTrace(start, gate, qargs) {
    validateOperation(start, gate, qargs);
    const s = clone(start);
    s.action = "insert";
    s.currentOperation = { type: "insert", gate, qargs: clone(qargs) };
    const trace = [];
    const id = s.nextId;
    const roles = gate === "CNOT"
      ? `q${qargs[0]} is the control and q${qargs[1]} is the target.`
      : gate === "CCNOT"
        ? `q${qargs[0]} and q${qargs[1]} are controls; q${qargs[2]} is the target.`
        : `The gate acts on q${qargs[0]}.`;
    const connections = qargs.map(q => {
      const target = outputId(s, q);
      return { q, predecessor: predecessorOf(s, target, q), target };
    });

    s.nodes.push({ id, type: "operation", gate, qargs: clone(qargs), label: gate, active: true });
    addStep(
      trace, s,
      "Stage 1 of 4 — add the new node",
      `A fresh ${gate} operation node is added to the node table and shown beside its future wire location. ${roles}`,
      [`new node ${id}`, `qargs = [${qargs.join(", ")}]`],
      [id], [], { kind: "add", nodeIds: [id], description: `Add node ${id} containing ${gate}.` }
    );

    const removedKeys = [];
    const incomingKeys = [];
    for (const { q, predecessor, target } of connections) {
      const removed = { source: predecessor, target, wire: q };
      const incoming = { source: predecessor, target: id, wire: q };
      s.edges = s.edges.filter(e => edgeKey(e) !== edgeKey(removed));
      s.edges.push(incoming);
      removedKeys.push(edgeKey(removed));
      incomingKeys.push(edgeKey(incoming));
    }
    addStep(
      trace, s,
      "Stage 2 of 4 — connect the predecessors",
      `The old final edge on each affected wire is cut. A new edge is drawn from each previous wire endpoint into node ${id}.`,
      connections.map(({ q, predecessor }) => `q${q}: ${predecessor} → ${id}`),
      [id], [...removedKeys, ...incomingKeys]
    );

    const outgoingKeys = [];
    for (const { q, target } of connections) {
      const outgoing = { source: id, target, wire: q };
      s.edges.push(outgoing);
      outgoingKeys.push(edgeKey(outgoing));
    }
    addStep(
      trace, s,
      "Stage 3 of 4 — connect the successors",
      `A second edge is drawn from node ${id} to each original successor. The affected paths are now structurally complete.`,
      connections.map(({ q, target }) => `q${q}: ${id} → ${target}`),
      [id], outgoingKeys
    );

    for (const q of qargs) s.frontier[q] = id;
    s.nextId += 1;
    addStep(
      trace, s,
      "Stage 4 of 4 — insertion complete",
      s.kind === "qiskit"
        ? `The ${gate} node is now part of the DAG. Temporary construction emphasis is removed and the derived wire endpoints are refreshed.`
        : `The ${gate} node is now part of the circuit. The frontier points to it on every affected wire and next_id advances to ${s.nextId}.`,
      [`${gate} inserted`, `next_id = ${s.nextId}`],
      [], [...incomingKeys, ...outgoingKeys]
    );
    return { trace, final: clone(s), nodeId: id };
  }

  function deleteTrace(start, id) {
    const s = clone(start);
    const node = opAt(s, id);
    if (!node) throw new Error(`Node ${id} is not an active operation node.`);
    s.action = "delete";
    s.currentOperation = { type: "delete", gate: node.gate, qargs: clone(node.qargs) };
    s.deletingNodeId = id;
    const trace = [];
    addStep(trace, s, `Confirm operation node ${id}`, s.kind === "qiskit"
      ? "The selected item must be an operation node. Its incoming and outgoing wire edges are then inspected."
      : "The selected table entry is checked to confirm that it contains an operation before deletion proceeds.",
      [`selected = ${node.gate}`, `qargs = [${node.qargs.join(", ")}]`], [id]);
    for (const q of node.qargs) {
      const pred = predecessorOf(s, id, q);
      const succ = successorOf(s, id, q);
      addStep(trace, s, `Find neighbours on q${q}`, `The local wire segment is ${pred} → ${id} → ${succ}.`, [`predecessor = ${pred}`, `successor = ${succ}`], [pred, id, succ]);
      const a = { source: pred, target: id, wire: q };
      const b = { source: id, target: succ, wire: q };
      s.edges = s.edges.filter(e => edgeKey(e) !== edgeKey(a) && edgeKey(e) !== edgeKey(b));
      addStep(trace, s, `Remove node ${id}'s q${q} edges`, "Both incident edges on this wire are removed.", [`− ${edgeKey(a)}`, `− ${edgeKey(b)}`], [id], [edgeKey(a), edgeKey(b)]);
      const joined = { source: pred, target: succ, wire: q };
      s.edges.push(joined);
      if (s.frontier[q] === id) s.frontier[q] = pred;
      addStep(trace, s, `Reconnect q${q}`, "The surviving predecessor is connected directly to the surviving successor.", [`+ ${edgeKey(joined)}`, `${s.kind === "isabelle" ? "frontier" : "end point"} q${q} ↦ ${s.frontier[q]}`], [pred, succ], [edgeKey(joined)]);
    }
    nodeAt(s, id).active = false;
    addStep(trace, s, `Remove node-table entry ${id}`, s.kind === "qiskit"
      ? "The operation node is removed after its quantum wires have been reconnected."
      : `The nodes function is updated to map NodeId ${id} to None. next_id remains ${s.nextId}, so IDs stay monotonic.`,
      [`nodes[${id}] = ${s.kind === "isabelle" ? "None" : "removed"}`, `next_id unchanged (${s.nextId})`], [id], [],
      { kind: "delete", nodeIds: [id], description: `Remove node-table entry ${id}.` });
    return { trace, final: clone(s) };
  }

  function replaceTrace(start, id, gate) {
    const s = clone(start);
    const node = opAt(s, id);
    if (!node) throw new Error(`Node ${id} is not an active operation node.`);
    if (!GATES[gate] || GATES[gate].arity !== node.qargs.length) throw new Error(`Replacement must have the same ${node.qargs.length}-qubit shape.`);
    s.action = "replace";
    s.currentOperation = { type: "replace", oldGate: node.gate, gate, qargs: clone(node.qargs) };
    const trace = [];
    addStep(trace, s, `Check replacement shape`, s.kind === "qiskit"
      ? "The new gate must fit the selected location, so it keeps the old node's ordered qubits."
      : "The replacement must use exactly the same ordered qubits because the surrounding edges are not changed.",
      [`old = ${node.gate}`, `new = ${gate}`, `qargs preserved`], [id]);
    const old = node.gate;
    addStep(trace, s, `Locate node-table row ${id}`,
      `The row still contains ${old}. It is highlighted so the value about to change is clear before the update happens.`,
      [`row ${id} selected`, `stored value is still ${old}`], [id], [],
      { kind: "inspect", nodeIds: [id], description: `Highlight node-table row ${id}.` });
    node.gate = gate;
    node.label = gate;
    addStep(trace, s, `Replace ${old} with ${gate}`, s.kind === "qiskit"
      ? "The operation changes while its qargs and incident wire connections remain at the same location."
      : "Only this node-table value changes. The edges, qubit count, and next available ID remain unchanged.",
      [`nodes[${id}]: ${old} → ${gate}`, "edges unchanged", "ordered qargs unchanged"], [id], [],
      { kind: "update", nodeIds: [id], description: `Change node ${id} from ${old} to ${gate}.` });
    return { trace, final: clone(s) };
  }

  function subcircuitTraceLegacy(start, id) {
    const s = clone(start);
    const target = opAt(s, id);
    if (!target) throw new Error(`Node ${id} is not an active operation node.`);
    s.action = "subcircuit";
    s.currentOperation = { type: "subcircuit", gate: target.gate, qargs: clone(target.qargs) };
    const trace = [];
    const qargs = clone(target.qargs);
    const neighbours = {};
    qargs.forEach(q => { neighbours[q] = { pred: predecessorOf(s, id, q), succ: successorOf(s, id, q) }; });
    addStep(trace, s, "Validate replacement interface", s.kind === "qiskit"
      ? "The replacement graph's qubits are mapped, in order, onto the qubits used by the selected node."
      : "The replacement graph and its declared input and output connections must match the selected location.",
      [`interface = [${qargs.join(", ")}]`, "replacement operations = 2"], [id]);

    target.active = false;
    s.edges = s.edges.filter(e => e.source !== id && e.target !== id);
    addStep(trace, s, `Remove original node ${id}`, s.kind === "qiskit"
      ? "The target operation and its incident edges are removed while its external neighbours are retained."
      : "The original node is marked absent and all its incident edges are removed, leaving its external neighbours available for reconnection.",
      [`nodes[${id}] removed`, "incident edges removed"], [id], [],
      { kind: "delete", nodeIds: [id], description: `Remove original node ${id}.` });

    const firstId = s.nextId++;
    const secondId = s.nextId++;
    const firstGate = "H";
    const secondGate = target.gate;
    s.nodes.push({ id: firstId, type: "operation", gate: firstGate, qargs: [qargs[0]], label: firstGate, active: true });
    s.nodes.push({ id: secondId, type: "operation", gate: secondGate, qargs, label: secondGate, active: true });
    addStep(trace, s, "Copy and rename replacement nodes", s.kind === "qiskit"
      ? "Fresh DAGOpNodes are inserted for the mini-DAG operations."
      : `Local replacement IDs are renamed above the host next_id, producing collision-free IDs ${firstId} and ${secondId}.`,
      [`+ node ${firstId}: H(q${qargs[0]})`, `+ node ${secondId}: ${secondGate}`], [firstId, secondId], [],
      { kind: "add", nodeIds: [firstId, secondId], description: `Add replacement nodes ${firstId} and ${secondId}.` });

    const internal = { source: firstId, target: secondId, wire: qargs[0] };
    s.edges.push(internal);
    addStep(trace, s, "Insert internal mini-DAG edges", "The replacement's own operation-to-operation connection is copied onto the host wire.", [`+ ${edgeKey(internal)}`], [firstId, secondId], [edgeKey(internal)]);

    qargs.forEach(q => {
      const entry = q === qargs[0] ? firstId : secondId;
      const incoming = { source: neighbours[q].pred, target: entry, wire: q };
      s.edges.push(incoming);
    });
    addStep(trace, s, "Connect host inputs", "Each original predecessor is connected to the declared input interface on its wire.", qargs.map(q => `q${q}: ${neighbours[q].pred} → ${q === qargs[0] ? firstId : secondId}`), [firstId, secondId]);

    qargs.forEach(q => {
      const outgoing = { source: secondId, target: neighbours[q].succ, wire: q };
      s.edges.push(outgoing);
    });
    addStep(trace, s, "Connect host outputs", "The replacement's output interface is connected to each original successor.", qargs.map(q => `q${q}: ${secondId} → ${neighbours[q].succ}`), [secondId]);

    qargs.forEach(q => { if (s.frontier[q] === id) s.frontier[q] = secondId; });
    addStep(trace, s, s.kind === "isabelle" ? "Update frontier" : "Substitution is complete", s.kind === "isabelle"
      ? "Each affected frontier entry now points to the final replacement node on that wire."
      : "The original location now contains a two-operation mini-DAG with the same external wire interface.",
      qargs.map(q => `q${q} end point ↦ ${s.frontier[q]}`), [firstId, secondId]);
    return { trace, final: clone(s), nodeIds: [firstId, secondId] };
  }

  function subcircuitTrace(start, id, replacementOps) {
    const s = clone(start);
    const target = opAt(s, id);
    if (!target) throw new Error(`Node ${id} is not an active operation node.`);
    if (!Array.isArray(replacementOps) || replacementOps.length < 1) throw new Error("Add at least one operation to the replacement DAG.");
    const interfaceQubits = new Set(target.qargs);
    replacementOps.forEach((op, index) => {
      if (!GATES[op.gate]) throw new Error(`Replacement operation ${index + 1} has an unknown gate.`);
      if (op.qargs.length !== GATES[op.gate].arity) throw new Error(`${op.gate} requires ${GATES[op.gate].arity} qubits.`);
      if (new Set(op.qargs).size !== op.qargs.length) throw new Error(`Replacement operation ${index + 1} repeats a qubit.`);
      if (op.qargs.some(q => !interfaceQubits.has(q))) throw new Error(`Replacement operations may use only qargs [${target.qargs.join(", ")}].`);
    });
    target.qargs.forEach(q => {
      if (!replacementOps.some(op => op.qargs.includes(q))) throw new Error(`The replacement DAG must use interface qubit q${q}.`);
    });

    s.action = "subcircuit";
    s.currentOperation = {
      type: "subcircuit",
      gate: target.gate,
      qargs: clone(target.qargs),
      replacement: replacementOps.map(op => op.gate)
    };
    const trace = [];
    const neighbours = {};
    target.qargs.forEach(q => { neighbours[q] = { pred: predecessorOf(s, id, q), succ: successorOf(s, id, q) }; });
    addStep(trace, s, "Validate chosen replacement DAG",
      `The selected ${replacementOps.length}-operation DAG uses exactly the host interface [${target.qargs.map(q => `q${q}`).join(", ")}].`,
      replacementOps.map((op, i) => `${i + 1}. ${op.gate}(${op.qargs.map(q => `q${q}`).join(", ")})`), [id]);

    target.active = false;
    s.edges = s.edges.filter(e => e.source !== id && e.target !== id);
    addStep(trace, s, `Remove original node ${id}`,
      "The original operation and its incident edges are removed while all external neighbours are retained.",
      [`node ${id} removed`, "incident edges removed"], [id], [],
      { kind: "delete", nodeIds: [id], description: `Remove original node ${id}.` });

    const inserted = replacementOps.map(op => {
      const node = { id: s.nextId++, type: "operation", gate: op.gate, qargs: clone(op.qargs), label: op.gate, active: true };
      s.nodes.push(node);
      return node;
    });
    addStep(trace, s, "Copy the chosen replacement nodes",
      "Each builder row becomes a fresh operation node with a collision-free host ID.",
      inserted.map(n => `+ node ${n.id}: ${n.gate}(${n.qargs.map(q => `q${q}`).join(", ")})`),
      inserted.map(n => n.id), [],
      { kind: "add", nodeIds: inserted.map(n => n.id), description: `Add ${inserted.length} chosen replacement operation${inserted.length === 1 ? "" : "s"}.` });

    const internalEdges = [];
    target.qargs.forEach(q => {
      const onWire = inserted.filter(n => n.qargs.includes(q));
      for (let i = 0; i < onWire.length - 1; i += 1) {
        internalEdges.push({ source: onWire[i].id, target: onWire[i + 1].id, wire: q });
      }
    });
    s.edges.push(...internalEdges);
    addStep(trace, s, "Insert internal DAG edges",
      "Operations that share an interface wire are connected in the order chosen in the builder.",
      internalEdges.map(edgeKey), inserted.map(n => n.id), internalEdges.map(edgeKey));

    const inputEdges = [];
    target.qargs.forEach(q => {
      const first = inserted.find(n => n.qargs.includes(q));
      inputEdges.push({ source: neighbours[q].pred, target: first.id, wire: q });
    });
    s.edges.push(...inputEdges);
    addStep(trace, s, "Connect host inputs",
      "Each original predecessor is connected to the first chosen operation on that interface wire.",
      inputEdges.map(edgeKey), inserted.map(n => n.id), inputEdges.map(edgeKey));

    const outputEdges = [];
    target.qargs.forEach(q => {
      const onWire = inserted.filter(n => n.qargs.includes(q));
      const last = onWire[onWire.length - 1];
      outputEdges.push({ source: last.id, target: neighbours[q].succ, wire: q });
      if (s.frontier[q] === id) s.frontier[q] = last.id;
    });
    s.edges.push(...outputEdges);
    addStep(trace, s, "Connect host outputs",
      "The final chosen operation on each interface wire is connected to the original successor.",
      outputEdges.map(edgeKey), inserted.map(n => n.id), outputEdges.map(edgeKey));

    addStep(trace, s, s.kind === "isabelle" ? "Update frontier and finish" : "Substitution is complete",
      s.kind === "isabelle"
        ? "Affected frontier entries now point to the chosen DAG's output-interface nodes."
        : "The chosen replacement DAG now occupies the original node's location and interface.",
      target.qargs.map(q => `q${q} end point = ${s.frontier[q]}`), [], [...internalEdges, ...inputEdges, ...outputEdges].map(edgeKey));
    return { trace, final: clone(s), nodeIds: inserted.map(n => n.id) };
  }

  class CircuitEngine {
    constructor(kind, n = 3) { this.kind = kind; this.state = makeInitial(kind, n); }
    initialize(n) { this.state = makeInitial(this.kind, n); return this.state; }
    insert(gate, qargs) { const result = insertTraceLegacy(this.state, gate, qargs); this.state = result.final; return result; }
    delete(id) { const result = deleteTrace(this.state, id); this.state = result.final; return result; }
    replaceGate(id, gate) { const result = replaceTrace(this.state, id, gate); this.state = result.final; return result; }
    replaceWithSubcircuit(id, replacementOps) { const result = subcircuitTrace(this.state, id, replacementOps); this.state = result.final; return result; }
    load(state) { this.state = clone(state); }
  }

  const PROOFS = {
    initial: {
      title: "The initial circuit is structurally valid",
      bullets: [
        "Every qubit has its canonical input, output, and one connecting edge.",
        "Boundary nodes and edges are well formed.",
        "The graph is acyclic and every wire is linear.",
        "The initial frontier and fresh-ID construction state are valid."
      ],
      names: ["initial_circuit_is_well_formed", "initial_circuit_is_acyclic", "initial_circuit_has_linear_wires", "initial_frontier_is_valid", "initial_next_id_is_unused"]
    },
    insert: {
      title: "Insertion preserves a valid circuit",
      bullets: [
        "The operation is stored at a fresh node ID and unrelated nodes/wires are unchanged.",
        "The frontier and monotonic node-allocation invariants are preserved.",
        "Well-formedness, acyclicity, and wire linearity are preserved.",
        "Together these results prove that inserting a valid operation preserves circuit validity."
      ],
      names: ["insert_operation_preserves_valid_frontier", "insert_operation_preserves_other_nodes", "insert_operation_preserves_node_id_allocation", "insert_operation_preserves_well_formed_circuit", "insert_operation_preserves_acyclicity", "insert_operation_preserves_wire_linearity", "insert_operation_preserves_valid_quantum_circuit"]
    },
    delete: {
      title: "Deletion preserves the surviving structure",
      bullets: [
        "Affected wires are reconnected and unrelated structure remains unchanged.",
        "Boundary nodes, remaining operations, num_qubits, and monotonic next_id are preserved.",
        "Surviving reachability, well-formedness, acyclicity, and wire linearity are preserved.",
        "Therefore deleting an existing operation from a valid circuit leaves a valid circuit."
      ],
      names: ["delete_operation_preserves_boundary_nodes", "delete_operation_preserves_operation_nodes", "delete_operation_preserves_next_id", "delete_operation_preserves_surviving_wire_reachability", "delete_operation_preserves_well_formed_circuit", "delete_operation_preserves_acyclicity", "delete_operation_preserves_wire_linearity", "delete_operation_preserves_valid_circuit"]
    },
    replace: {
      title: "Same-interface replacement preserves validity",
      bullets: [
        "Only the selected operation value changes; its ordered qubit interface stays fixed.",
        "All edges, other nodes, num_qubits, and next_id remain unchanged.",
        "Matching qargs preserve wire usage, well-formedness, acyclicity, and linearity.",
        "The replacement therefore preserves a valid circuit."
      ],
      names: ["replacement_preserves_other_nodes", "replacement_preserves_edges", "replacement_preserves_num_qubits", "replacement_preserves_next_id", "replacement_preserves_well_formed_circuit", "replacement_preserves_acyclicity", "replacement_preserves_wire_linearity", "replacement_preserves_valid_circuit"]
    },
    subcircuit: {
      title: "Subcircuit replacement: major structural results completed",
      bullets: [
        "Replacement nodes are renamed to avoid collision and interfaces reconnect to the host wires.",
        "Unrelated nodes/edges and canonical boundary nodes are preserved.",
        "Well-formedness and acyclicity preservation are proven.",
        "Remaining proof obligation: a single final theorem combining every validity component is not present in the current theory."
      ],
      names: ["replace_operation_by_subcircuit_preserves_unrelated_nodes", "replace_operation_by_subcircuit_preserves_unrelated_edges", "replace_operation_by_subcircuit_preserves_boundary_nodes", "replace_operation_by_subcircuit_preserves_well_formed_circuit", "replace_operation_by_subcircuit_preserves_acyclicity"]
    },
    loaded: {
      title: "The complete gate sequence remains a valid circuit",
      bullets: [
        "The graph begins from the valid four-qubit initial circuit.",
        "Each S, T, single-qubit, and CNOT operation is inserted using the verified insertion transformation.",
        "Repeated preservation means the resulting unitary gate sequence remains well formed, acyclic, and wire-linear.",
        "Measurements are not claimed because the current formal circuit model has no measurement or classical-bit nodes."
      ],
      names: ["initial_construction_state_is_valid", "insert_operation_preserves_valid_quantum_circuit"]
    }
  };

  const QISKIT_RESULTS = {
    initial: {
      title: "The empty Qiskit DAG is ready for operations",
      bullets: [
        "Every qubit has an input node, an output node, and one directed connection.",
        "There are no operation nodes yet.",
        "The displayed end-point entry is the node immediately before each output."
      ]
    },
    insert: {
      title: "The operation is appended at the output side",
      bullets: [
        "Qiskit validates the ordered qubits and allocates a new operation node.",
        "On every affected wire, the old final edge is replaced by two edges through the new node.",
        "Unaffected wires and existing operation nodes are left unchanged."
      ]
    },
    delete: {
      title: "The operation is removed and its wires are rejoined",
      bullets: [
        "Qiskit reads the immediate predecessor and successor on every affected wire.",
        "The selected operation and its incident edges are removed.",
        "Each predecessor is connected directly to its corresponding successor."
      ]
    },
    replace: {
      title: "The gate changes without moving the node",
      bullets: [
        "The replacement must have a compatible shape.",
        "The existing ordered qubits and incident wire connections are retained.",
        "Only the operation stored at the selected location changes."
      ]
    },
    subcircuit: {
      title: "The replacement DAG occupies the original interface",
      bullets: [
        "Replacement wires are mapped onto the selected node's wires.",
        "The replacement operation nodes and internal edges are copied into the host DAG.",
        "The original external predecessors and successors are reconnected to the replacement."
      ]
    },
    loaded: {
      title: "The four-qubit Qiskit DAG contains the requested gate sequence",
      bullets: [
        "The two requested CZ positions are represented as CNOT operations with the same ordered qubits.",
        "S and T are ordinary one-qubit operation nodes.",
        "The measurement statements are omitted because this demonstrator does not model classical wires."
      ]
    }
  };

  global.DagDemo = { GATES, CircuitEngine, PROOFS, QISKIT_RESULTS, helpers: { clone, edgeKey, activeNodes, opAt } };
}(window));
