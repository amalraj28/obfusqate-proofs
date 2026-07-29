const fs = require("node:fs");
const vm = require("node:vm");
const assert = require("node:assert/strict");

const context = { window: {} };
vm.createContext(context);
vm.runInContext(fs.readFileSync(__dirname + "/engine.js", "utf8"), context);
const { CircuitEngine } = context.window.DagDemo;

function edge(state, source, target, wire) {
  return state.edges.some(e => e.source === source && e.target === target && e.wire === wire);
}

for (const n of [1, 3, 8]) {
  const i = new CircuitEngine("isabelle", n);
  assert.equal(i.state.nodes.length, 2 * n);
  assert.equal(i.state.edges.length, n);
  assert.equal(i.state.nextId, 2 * n);
  for (let q = 0; q < n; q++) {
    assert.equal(i.state.frontier[q], 2 * q);
    assert.ok(edge(i.state, 2 * q, 2 * q + 1, q));
  }
}

{
  const q = new CircuitEngine("qiskit", 1).insert("H", [0]);
  const i = new CircuitEngine("isabelle", 1).insert("H", [0]);
  assert.deepEqual(Array.from(q.trace[0].state.currentOperation.qargs), [0]);
  assert.equal(q.trace[0].state.currentOperation.gate, "H");
  assert.notEqual(q.trace.length, i.trace.length);
  assert.match(q.trace.at(-1).title, /Append is complete/);
  assert.match(i.trace.at(-1).title, /Insertion is complete/);
  assert.ok(context.window.DagDemo.QISKIT_RESULTS.insert);
}

{
  for (const gate of ["S", "T"]) {
    const i = new CircuitEngine("isabelle", 1);
    const inserted = i.insert(gate, [0]);
    assert.equal(i.state.nodes.find(node => node.id === inserted.nodeId).gate, gate);
  }
}

{
  const i = new CircuitEngine("isabelle", 3);
  const h = i.insert("H", [0]);
  assert.equal(h.nodeId, 6);
  assert.equal(i.state.frontier[0], 6);
  assert.ok(edge(i.state, 0, 6, 0));
  assert.ok(edge(i.state, 6, 1, 0));
  const cx = i.insert("CNOT", [0, 1]);
  assert.deepEqual(Array.from(i.state.nodes.find(n => n.id === cx.nodeId).qargs), [0, 1]);
  assert.equal(i.state.nodes.filter(n => n.id === cx.nodeId).length, 1);
  assert.equal(i.state.edges.filter(e => e.target === cx.nodeId).length, 2);
  assert.equal(i.state.edges.filter(e => e.source === cx.nodeId).length, 2);
  assert.match(cx.trace[0].explanation, /q0 is the control and q1 is the target/);
  assert.ok(cx.trace.length > 4);
  assert.match(cx.trace.at(-1).title, /Insertion is complete/);
  assert.equal(i.state.frontier[0], cx.nodeId);
  assert.equal(i.state.frontier[1], cx.nodeId);
  assert.throws(() => i.insert("CNOT", [1, 1]), /distinct/);
  assert.throws(() => i.insert("H", [3]), /between/);
}

{
  const i = new CircuitEngine("isabelle", 1);
  const a = i.insert("H", [0]).nodeId;
  const b = i.insert("X", [0]).nodeId;
  const c = i.insert("Z", [0]).nodeId;
  const next = i.state.nextId;
  const deletion = i.delete(b);
  assert.ok(deletion.trace.every(frame => frame.state.deletingNodeId === b));
  assert.ok(edge(i.state, a, c, 0));
  assert.equal(i.state.nextId, next);
  assert.equal(i.state.nodes.find(n => n.id === b).active, false);
}

{
  const i = new CircuitEngine("isabelle", 2);
  const id = i.insert("CNOT", [0, 1]).nodeId;
  const before = JSON.stringify(i.state.edges);
  i.replaceGate(id, "CNOT");
  assert.equal(JSON.stringify(i.state.edges), before);
  assert.throws(() => i.replaceGate(id, "H"), /same 2-qubit shape/);
}

{
  const i = new CircuitEngine("isabelle", 1);
  const id = i.insert("H", [0]).nodeId;
  const replacement = i.replaceGate(id, "X");
  assert.equal(replacement.trace.length, 3);
  assert.equal(replacement.trace[1].state.nodes.find(n => n.id === id).gate, "H");
  assert.equal(replacement.trace[1].state.tableChange.kind, "inspect");
  assert.equal(replacement.trace[2].state.nodes.find(n => n.id === id).gate, "X");
}

{
  const i = new CircuitEngine("isabelle", 2);
  const id = i.insert("CNOT", [0, 1]).nodeId;
  const result = i.replaceWithSubcircuit(id, [
    { gate: "H", qargs: [0] },
    { gate: "CNOT", qargs: [0, 1] }
  ]);
  assert.equal(result.nodeIds.length, 2);
  assert.equal(new Set(i.state.nodes.map(n => n.id)).size, i.state.nodes.length);
  assert.equal(i.state.frontier[0], result.nodeIds[1]);
  assert.equal(i.state.frontier[1], result.nodeIds[1]);
  assert.ok(edge(i.state, result.nodeIds[0], result.nodeIds[1], 0));
}

{
  const q = new CircuitEngine("qiskit", 1);
  const id = q.insert("X", [0]).nodeId;
  const result = q.replaceWithSubcircuit(id, [
    { gate: "H", qargs: [0] },
    { gate: "Z", qargs: [0] },
    { gate: "Y", qargs: [0] }
  ]);
  assert.equal(result.nodeIds.length, 3);
  assert.ok(edge(q.state, result.nodeIds[0], result.nodeIds[1], 0));
  assert.ok(edge(q.state, result.nodeIds[1], result.nodeIds[2], 0));
}

{
  const q = new CircuitEngine("qiskit", 3);
  const i = new CircuitEngine("isabelle", 3);
  q.insert("CCNOT", [0, 1, 2]);
  i.insert("CCNOT", [0, 1, 2]);
  const normalize = state => state.edges.map(e => `${e.wire}:${state.nodes.find(n => n.id === e.source).type}->${state.nodes.find(n => n.id === e.target).type}`).sort();
  assert.deepEqual(normalize(q.state), normalize(i.state));
}

{
  const operations = [
    ["S", [0]], ["Y", [1]], ["S", [2]], ["Z", [3]],
    ["CNOT", [2, 3]], ["X", [0]], ["X", [1]], ["Z", [2]], ["T", [3]],
    ["CNOT", [0, 2]], ["X", [0]], ["T", [1]], ["T", [2]], ["Y", [3]],
    ["CNOT", [2, 0]], ["Z", [0]], ["Z", [1]], ["S", [2]], ["T", [3]],
    ["CNOT", [1, 0]]
  ];
  for (const kind of ["qiskit", "isabelle"]) {
    const engine = new CircuitEngine(kind, 4);
    const walkthrough = operations.flatMap(([gate, qargs]) => engine.insert(gate, qargs).trace);
    const operationCount = state => state.nodes.filter(node => node.active && node.type === "operation").length;
    assert.equal(operationCount(walkthrough[0].state), 0);
    assert.equal(operationCount(walkthrough.at(-1).state), 20);
    assert.equal(operationCount(engine.state), 20);
    assert.equal(engine.state.nodes.length, 28);
    assert.equal(engine.state.edges.length, 28);
    assert.ok(walkthrough.length > operations.length);
  }
}

{
  const fixtures = JSON.parse(fs.readFileSync(__dirname + "/fixtures/qiskit-2.4.1.json", "utf8"));
  const q = new CircuitEngine("qiskit", 3);
  const normalized = state => state.edges.map(e => {
    const source = state.nodes.find(n => n.id === e.source);
    const target = state.nodes.find(n => n.id === e.target);
    const name = n => n.type === "operation" ? n.gate : n.type;
    return `q${e.wire}:${name(source)}->${name(target)}`;
  }).sort();
  assert.equal(JSON.stringify(normalized(q.state)), JSON.stringify(fixtures.normalized_scenarios.empty_3.slice().sort()));
  q.insert("H", [0]);
  assert.equal(JSON.stringify(normalized(q.state)), JSON.stringify(fixtures.normalized_scenarios.insert_h_q0.slice().sort()));
  q.insert("CNOT", [0, 1]);
  assert.equal(JSON.stringify(normalized(q.state)), JSON.stringify(fixtures.normalized_scenarios.insert_cx_q0_q1_after_h.slice().sort()));
}

console.log("All DAG visual demonstrator tests passed.");
