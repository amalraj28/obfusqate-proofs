# Compact Isabelle theory generator

Generate the AI context file once from PowerShell or a terminal at the repository root:

```powershell
python scripts/generate_ai_theory.py QuantumCircuit.thy generated/QuantumCircuit_Skeleton.thy
```

Keep it synchronized while editing:

```powershell
python scripts/watch_ai_theory.py QuantumCircuit.thy generated/QuantumCircuit_Skeleton.thy
```

Stop the watcher with `Ctrl+C`. It uses polling and a short debounce, so it detects ordinary saves as well as editor rename-and-replace saves on Windows. Output is written to a temporary file in `generated/` and atomically replaced only after successful generation.

The tools require Python 3.9 or newer and use only the Python standard library. Run the tests with:

```powershell
python -m unittest scripts/test_generate_ai_theory.py
```

The generated theory omits all Isabelle comments and replaces theorem proofs with `sorry`. Supported proof forms are `by`, nested `proof ... qed`, `apply ... done`, `apply ... by`, `sorry`, and `oops`, optionally preceded by `using`, `unfolding`, `supply`, or `including`. Comment-like text inside strings and ASCII or Unicode cartouches is preserved; nested comments are supported.

Known unsupported syntax: terminal Isar proofs using standalone `.` or `..`, `defer`/`prefer` scripts without a final `done`, custom outer-syntax theorem commands, and theorem declarations whose proof and the following outer declaration share one physical line. The generator fails instead of replacing the existing output when it cannot identify a supported proof boundary.
