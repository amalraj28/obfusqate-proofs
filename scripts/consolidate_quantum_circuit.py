import hashlib
import json
import re
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
AUTHORITATIVE = ROOT / "QuantumCircuit.thy"
AUTHORITATIVE_COPY = ROOT / "work" / "QuantumCircuit_authoritative_copy.thy"
SKELETON = ROOT / "work" / "QuantumCircuit_Skeleton_work.thy"
SOURCE_MAP = ROOT / "manifests" / "source_map.json"
PROVED_DIR = ROOT / "generated" / "theories"
SKELETON_DIR = ROOT / "generated" / "skeleton"

EXPECTED_AUTHORITATIVE_SHA256 = (
    "124d16dcd78b621ac1c0d2e7a94638ae83401b001007aa96a7eabe582fa77813"
)
EXPECTED_SKELETON_SHA256 = (
    "19be416dd8983c90ec7c968f392f3d491c301f7fe0481b7afb8fc57d47dd017b"
)
EXPECTED_SOURCE_MAP_SHA256 = (
    "e3299be7c87c0fab7f9ae0dcf9a89af909448da423a89463063945daaf0809d2"
)

CONTENT_KINDS = {
    "datatype",
    "record",
    "type_synonym",
    "definition",
    "fun",
    "lemma",
    "theorem",
    "corollary",
    "proposition",
    "interpretation",
    "section",
}
PROOF_KINDS = {"lemma", "theorem", "corollary", "proposition", "interpretation"}
HEADER_RE = re.compile(r"^(" + "|".join(sorted(CONTENT_KINDS)) + r")\b")
PROOF_START_RE = re.compile(r"^\s*(?:proof|by|sorry|oops)\b")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def ids(*ranges: tuple[int, int], singles: tuple[int, ...] = ()) -> list[int]:
    result = [command_id for start, end in ranges for command_id in range(start, end + 1)]
    result.extend(singles)
    return result


GROUPS = [
    {
        "theory": "Quantum_Circuit_Data",
        "imports": ["Complex_Main"],
        "ids": ids((4, 30)),
    },
    {
        "theory": "Quantum_Circuit_Graph",
        "imports": ["Quantum_Circuit_Data"],
        "ids": ids((31, 60), (131, 140)),
    },
    {
        "theory": "Quantum_Circuit_State",
        "imports": ["Quantum_Circuit_Graph"],
        "ids": ids((61, 85)),
    },
    {
        "theory": "Quantum_Circuit_Insertion",
        "imports": ["Quantum_Circuit_State"],
        "ids": ids((86, 128), singles=(130,)),
    },
    {
        "theory": "Quantum_Circuit_Deletion",
        "imports": ["Quantum_Circuit_State"],
        "ids": ids((141, 194)),
    },
    {
        "theory": "Quantum_Circuit_Replacement",
        "imports": ["Quantum_Circuit_State"],
        "ids": ids((196, 213), (215, 318)),
    },
    {
        "theory": "QuantumCircuit",
        "skeleton_theory": "QuantumCircuit_Skeleton",
        "imports": [
            "Quantum_Circuit_Insertion",
            "Quantum_Circuit_Deletion",
            "Quantum_Circuit_Replacement",
        ],
        "ids": [129, 195, 214],
    },
    {
        "theory": "Quantum_Circuit_Examples",
        "imports": ["QuantumCircuit"],
        "skeleton_imports": ["QuantumCircuit_Skeleton"],
        "ids": [319, 320],
    },
]


def command_name(kind: str, header: str) -> str:
    rest = header[len(kind) :].strip()
    if kind == "section":
        return rest
    match = re.match(r"([^\s:\[=]+)", rest)
    if not match:
        raise AssertionError(f"Cannot parse command name from: {header!r}")
    return match.group(1)


def parse_skeleton_commands(lines: list[str], mappings: list[list[object]]) -> dict[int, str]:
    starts: list[tuple[int, str, str]] = []
    for line_number, line in enumerate(lines):
        match = HEADER_RE.match(line)
        if match:
            kind = match.group(1)
            starts.append((line_number, kind, command_name(kind, line.rstrip("\r\n"))))

    expected = [
        (command_id, mapping[0], mapping[1])
        for command_id, mapping in enumerate(mappings, start=1)
        if mapping[0] in CONTENT_KINDS
    ]
    assert len(starts) == len(expected) == 317, (len(starts), len(expected))

    result: dict[int, str] = {}
    for index, ((start, kind, name), (command_id, expected_kind, expected_name)) in enumerate(
        zip(starts, expected, strict=True)
    ):
        assert kind == expected_kind, (command_id, kind, expected_kind)
        assert name == expected_name, (command_id, name, expected_name)
        end = starts[index + 1][0] if index + 1 < len(starts) else len(lines) - 1
        text = "".join(lines[start:end]).rstrip() + "\n"
        if kind in PROOF_KINDS:
            command_lines = text.splitlines(keepends=True)
            proof_start = next(
                (i for i, command_line in enumerate(command_lines[1:], start=1) if PROOF_START_RE.match(command_line)),
                None,
            )
            assert proof_start is not None, (command_id, kind, name)
            text = "".join(command_lines[:proof_start]).rstrip() + "\n  sorry\n"
        result[command_id] = text
    return result


def theory_header(theory: str, imports: list[str]) -> str:
    if len(imports) == 1:
        import_text = f"  imports {imports[0]}"
    else:
        import_text = "  imports\n" + "\n".join(f"    {item}" for item in imports)
    return f"theory {theory}\n{import_text}\n\nbegin\n\n"


def write_theory(path: Path, theory: str, imports: list[str], commands: list[str]) -> None:
    body = "\n".join(command.rstrip() for command in commands)
    path.write_text(theory_header(theory, imports) + body + "\n\nend\n", encoding="utf-8")


def output_inventory(output_dir: Path) -> Counter[tuple[str, str]]:
    inventory: Counter[tuple[str, str]] = Counter()
    for path in output_dir.glob("*.thy"):
        for line in path.read_text(encoding="utf-8").splitlines():
            match = HEADER_RE.match(line)
            if match:
                kind = match.group(1)
                inventory[(kind, command_name(kind, line))] += 1
    return inventory


def main() -> None:
    assert sha256(AUTHORITATIVE) == EXPECTED_AUTHORITATIVE_SHA256
    assert sha256(AUTHORITATIVE_COPY) == EXPECTED_AUTHORITATIVE_SHA256
    assert AUTHORITATIVE.read_bytes() == AUTHORITATIVE_COPY.read_bytes()
    assert sha256(SKELETON) == EXPECTED_SKELETON_SHA256
    assert sha256(SOURCE_MAP) == EXPECTED_SOURCE_MAP_SHA256

    source_map = json.loads(SOURCE_MAP.read_text(encoding="utf-8"))
    mappings = source_map["mappings"]
    assert source_map["validation"]["status"] == "passed"
    assert len(mappings) == 321

    owned = [command_id for group in GROUPS for command_id in group["ids"]]
    assert len(owned) == len(set(owned)) == 317
    assert sorted(owned) == list(range(4, 321))

    authoritative_lines = AUTHORITATIVE.read_text(encoding="utf-8").splitlines(keepends=True)
    authoritative_commands = {
        command_id: "".join(authoritative_lines[start - 1 : end]).rstrip() + "\n"
        for command_id, (_, _, start, end) in enumerate(mappings, start=1)
        if command_id in owned
    }
    skeleton_commands = parse_skeleton_commands(
        SKELETON.read_text(encoding="utf-8").splitlines(keepends=True), mappings
    )

    for output_dir in (PROVED_DIR, SKELETON_DIR):
        resolved = output_dir.resolve()
        assert resolved.parent == (ROOT / "generated").resolve()
        output_dir.mkdir(parents=True, exist_ok=True)
        for old_theory in output_dir.glob("*.thy"):
            old_theory.unlink()

    for group in GROUPS:
        proved_name = group["theory"]
        skeleton_name = group.get("skeleton_theory", proved_name)
        proved_imports = group["imports"]
        skeleton_imports = group.get("skeleton_imports", proved_imports)
        command_ids = group["ids"]
        write_theory(
            PROVED_DIR / f"{proved_name}.thy",
            proved_name,
            proved_imports,
            [authoritative_commands[command_id] for command_id in command_ids],
        )
        write_theory(
            SKELETON_DIR / f"{skeleton_name}.thy",
            skeleton_name,
            skeleton_imports,
            [skeleton_commands[command_id] for command_id in command_ids],
        )

    (PROVED_DIR / "ROOT").write_text(
        "session QuantumCircuit_Reorganized = HOL +\n"
        "  options [document = false]\n\n"
        "  theories\n"
        "    Quantum_Circuit_Examples\n",
        encoding="utf-8",
    )
    (SKELETON_DIR / "ROOT").write_text(
        "session QuantumCircuit_Reorganized_Skeleton = HOL +\n"
        "  options [document = false]\n\n"
        "  theories\n"
        "    Quantum_Circuit_Examples\n",
        encoding="utf-8",
    )

    proved_text = "\n".join(path.read_text(encoding="utf-8") for path in PROVED_DIR.glob("*.thy"))
    for forbidden in ("sorry", "oops", "axiomatization", "oracle", "skip_proof"):
        assert not re.search(rf"\b{forbidden}\b", proved_text), forbidden

    skeleton_text = "\n".join(path.read_text(encoding="utf-8") for path in SKELETON_DIR.glob("*.thy"))
    assert len(re.findall(r"^\s*sorry\s*$", skeleton_text, flags=re.MULTILINE)) == 223
    assert len(re.findall(r"^interpretation\b", skeleton_text, flags=re.MULTILINE)) == 2

    expected_inventory = Counter(
        (mappings[command_id - 1][0], mappings[command_id - 1][1]) for command_id in owned
    )
    assert output_inventory(PROVED_DIR) == expected_inventory
    assert output_inventory(SKELETON_DIR) == expected_inventory

    main_text = (PROVED_DIR / "QuantumCircuit.thy").read_text(encoding="utf-8")
    assert "Quantum_Circuit_Examples" not in main_text
    for theorem in (
        "insert_operation_preserves_valid_quantum_circuit",
        "delete_operation_preserves_valid_circuit",
        "replacement_preserves_valid_circuit",
    ):
        assert main_text.count(f"lemma {theorem}:") == 1
    assert "replace_operation_by_subcircuit_preserves_valid_circuit" not in proved_text

    print("generated 8 proved theories and 8 matching skeleton theories")


if __name__ == "__main__":
    main()
