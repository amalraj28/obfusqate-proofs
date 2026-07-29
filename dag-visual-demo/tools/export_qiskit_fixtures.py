"""Optional maintainer utility. Requires qiskit==2.4.1; the website does not."""
from __future__ import annotations

import json
from pathlib import Path

from qiskit.circuit import QuantumRegister
from qiskit.circuit.library import CXGate, HGate
from qiskit.dagcircuit import DAGCircuit


def snapshot(dag: DAGCircuit) -> dict:
    def node_value(node):
        value = {"id": node._node_id, "type": type(node).__name__}
        if hasattr(node, "op"):
            value["gate"] = node.op.name
            value["qargs"] = [dag.find_bit(q).index for q in node.qargs]
        elif hasattr(node, "wire"):
            value["wire"] = dag.find_bit(node.wire).index
        return value

    return {
        "qiskit_version": "2.4.1",
        "nodes": sorted((node_value(node) for node in dag.nodes()), key=lambda x: x["id"]),
        "edges": sorted(
            {
                "source": source._node_id,
                "target": target._node_id,
                "wire": dag.find_bit(wire).index,
            }
            for source, target, wire in dag.edges()
        ),
    }


def main() -> None:
    dag = DAGCircuit()
    q = QuantumRegister(3, "q")
    dag.add_qreg(q)
    fixtures = {"empty_3": snapshot(dag)}
    dag.apply_operation_back(HGate(), [q[0]])
    fixtures["insert_h_q0"] = snapshot(dag)
    dag.apply_operation_back(CXGate(), [q[0], q[1]])
    fixtures["insert_cx_q0_q1"] = snapshot(dag)
    target = Path(__file__).parents[1] / "fixtures" / "qiskit-2.4.1.json"
    target.parent.mkdir(exist_ok=True)
    target.write_text(json.dumps(fixtures, indent=2), encoding="utf-8")
    print(target)


if __name__ == "__main__":
    main()
