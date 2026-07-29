#!/usr/bin/env python3
"""Generate a proof- and comment-free Isabelle theory as compact AI context."""

from __future__ import annotations

import argparse
import os
import re
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


THEOREM_COMMANDS = {"lemma", "theorem", "proposition", "corollary"}
PROOF_PREFIXES = {"unfolding", "using", "supply", "including"}
PROOF_STARTERS = {"proof", "by", "apply", "sorry", "oops"}
OUTER_COMMANDS = {
    "abbreviation",
    "begin",
    "class",
    "context",
    "corollary",
    "datatype",
    "definition",
    "end",
    "experiment",
    "fun",
    "function",
    "global_interpretation",
    "inductive",
    "inductive_set",
    "instantiation",
    "interpretation",
    "lemma",
    "locale",
    "notepad",
    "overloading",
    "primrec",
    "proposition",
    "record",
    "sublocale",
    "termination",
    "theorem",
    "theory",
    "type_synonym",
    "typedef",
    "value",
}
WORD_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
COMMENT_MARKER = "\0"


class GenerationError(ValueError):
    """Raised when input cannot be transformed safely."""

    def __init__(
        self,
        message: str,
        *,
        line: int | None = None,
        context: str | None = None,
    ) -> None:
        super().__init__(message)
        self.line = line
        self.context = context


@dataclass(frozen=True)
class Token:
    value: str
    start: int
    end: int
    line_leading: bool


def _strip_isabelle_comments(text: str) -> str:
    """Remove comments without touching comment-like text in literals.

    A marker is used temporarily so lines containing only comments can be
    removed altogether. Inline comments become a single space, preserving
    their role as lexical separators without retaining multiline comment
    line breaks.
    """
    pieces: list[str] = []
    n = len(text)
    i = 0
    copied_until = 0

    while i < n:
        if text.startswith("(*", i):
            pieces.append(text[copied_until:i])
            depth = 1
            i += 2
            while i < n and depth:
                if text.startswith("(*", i):
                    depth += 1
                    i += 2
                elif text.startswith("*)", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise GenerationError("unterminated Isabelle comment")
            pieces.append(COMMENT_MARKER)
            copied_until = i
            continue

        if text[i] == '"':
            i += 1
            while i < n:
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            else:
                raise GenerationError("unterminated Isabelle string")
            continue

        if text.startswith("\\<open>", i):
            depth = 1
            i += len("\\<open>")
            while i < n and depth:
                if text.startswith("\\<open>", i):
                    depth += 1
                    i += len("\\<open>")
                elif text.startswith("\\<close>", i):
                    depth -= 1
                    i += len("\\<close>")
                else:
                    i += 1
            if depth:
                raise GenerationError("unterminated Isabelle cartouche")
            continue

        if text[i] == "‹":
            depth = 1
            i += 1
            while i < n and depth:
                if text[i] == "‹":
                    depth += 1
                elif text[i] == "›":
                    depth -= 1
                i += 1
            if depth:
                raise GenerationError("unterminated Isabelle cartouche")
            continue

        i += 1

    pieces.append(text[copied_until:])
    stripped = "".join(pieces)
    stripped = re.sub(
        rf"(?m)^[ \t]*(?:{re.escape(COMMENT_MARKER)}[ \t]*)+(?:\r?\n|$)",
        "",
        stripped,
    )
    stripped = re.sub(
        rf"[ \t]*{re.escape(COMMENT_MARKER)}[ \t]*(?=\r?$)",
        "",
        stripped,
        flags=re.MULTILINE,
    )

    compacted: list[str] = []
    for index, char in enumerate(stripped):
        if char != COMMENT_MARKER:
            compacted.append(char)
            continue
        before = stripped[index - 1] if index else ""
        after = stripped[index + 1] if index + 1 < len(stripped) else ""
        if before and after and not before.isspace() and not after.isspace():
            compacted.append(" ")
    return "".join(compacted)


def _mask_isabelle_literals(text: str) -> str:
    """Mask comments, strings, and cartouches while retaining offsets/newlines."""
    chars = list(text)
    masked = list(text)
    n = len(text)
    i = 0

    def blank(start: int, end: int) -> None:
        for index in range(start, end):
            if masked[index] not in "\r\n":
                masked[index] = " "

    while i < n:
        if text.startswith("(*", i):
            start = i
            depth = 1
            i += 2
            while i < n and depth:
                if text.startswith("(*", i):
                    depth += 1
                    i += 2
                elif text.startswith("*)", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise GenerationError("unterminated Isabelle comment")
            blank(start, i)
            continue

        if chars[i] == '"':
            start = i
            i += 1
            while i < n:
                if chars[i] == "\\":
                    i += 2
                elif chars[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            else:
                raise GenerationError("unterminated Isabelle string")
            blank(start, min(i, n))
            continue

        if text.startswith("\\<open>", i):
            start = i
            depth = 1
            i += len("\\<open>")
            while i < n and depth:
                if text.startswith("\\<open>", i):
                    depth += 1
                    i += len("\\<open>")
                elif text.startswith("\\<close>", i):
                    depth -= 1
                    i += len("\\<close>")
                else:
                    i += 1
            if depth:
                raise GenerationError("unterminated Isabelle cartouche")
            blank(start, i)
            continue

        if chars[i] == "‹":
            start = i
            depth = 1
            i += 1
            while i < n and depth:
                if chars[i] == "‹":
                    depth += 1
                elif chars[i] == "›":
                    depth -= 1
                i += 1
            if depth:
                raise GenerationError("unterminated Isabelle cartouche")
            blank(start, i)
            continue

        i += 1

    return "".join(masked)


def _tokens(masked: str) -> list[Token]:
    result: list[Token] = []
    for match in WORD_RE.finditer(masked):
        line_start = masked.rfind("\n", 0, match.start()) + 1
        leading = not masked[line_start : match.start()].strip()
        result.append(Token(match.group(), match.start(), match.end(), leading))
    return result


def _line_end(text: str, position: int) -> int:
    newline = text.find("\n", position)
    return len(text) if newline < 0 else newline


def _line_number(text: str, position: int) -> int:
    return text.count("\n", 0, position) + 1


def _line_excerpt(text: str, position: int, limit: int = 120) -> str:
    start = text.rfind("\n", 0, position) + 1
    end = _line_end(text, position)
    excerpt = text[start:end].strip()
    if len(excerpt) > limit:
        return excerpt[: limit - 3] + "..."
    return excerpt


def _balanced_by_end(masked: str, start: int, limit: int) -> int:
    pairs = {"(": ")", "[": "]", "{": "}"}
    closing = set(pairs.values())
    stack: list[str] = []
    i = start
    while i < limit:
        char = masked[i]
        if char in pairs:
            stack.append(pairs[char])
        elif char in closing:
            if not stack or stack.pop() != char:
                raise GenerationError("unbalanced delimiters in 'by' proof")
        elif char == "\n" and not stack:
            return i
        i += 1
    if stack:
        raise GenerationError("incomplete multiline 'by' proof")
    return limit


def _proof_end(
    text: str,
    masked: str,
    tokens: list[Token],
    starter_index: int,
    declaration_limit: int,
) -> int:
    starter = tokens[starter_index]
    if starter.value == "proof":
        depth = 0
        for token in tokens[starter_index:]:
            if token.start >= declaration_limit:
                break
            if token.value == "proof":
                depth += 1
            elif token.value == "qed":
                depth -= 1
                if depth == 0:
                    return _line_end(text, token.end)
        raise GenerationError("unterminated structured proof (missing qed)")

    if starter.value == "apply":
        for token in tokens[starter_index + 1 :]:
            if token.start >= declaration_limit:
                break
            if token.value == "done" and token.line_leading:
                return _line_end(text, token.end)
            if token.value == "by" and token.line_leading:
                return _balanced_by_end(masked, token.end, declaration_limit)
        raise GenerationError("unterminated apply proof (missing done or terminal by)")

    if starter.value == "by":
        return _balanced_by_end(masked, starter.end, declaration_limit)

    return _line_end(text, starter.end)  # sorry or oops


def _next_outer_declaration(tokens: list[Token], start_index: int) -> int:
    for token in tokens[start_index:]:
        if token.line_leading and token.value in OUTER_COMMANDS:
            return token.start
    return sys.maxsize


def transform_theory(text: str, output_theory_name: str) -> str:
    """Return a comment-free theory with theorem proofs replaced by ``sorry``."""
    source_text = text
    source_tokens = _tokens(_mask_isabelle_literals(source_text))
    source_theorems = [
        token
        for token in source_tokens
        if token.line_leading and token.value in THEOREM_COMMANDS
    ]
    text = _strip_isabelle_comments(text)
    masked = _mask_isabelle_literals(text)
    tokens = _tokens(masked)
    theory_tokens = [token for token in tokens if token.line_leading and token.value == "theory"]
    if len(theory_tokens) != 1:
        raise GenerationError("expected exactly one top-level theory declaration")

    theory_index = tokens.index(theory_tokens[0])
    if theory_index + 1 >= len(tokens):
        raise GenerationError("theory declaration has no name")
    old_name = tokens[theory_index + 1]

    replacements: list[tuple[int, int, str]] = [
        (old_name.start, old_name.end, output_theory_name)
    ]

    theorem_indices = [
        index
        for index, token in enumerate(tokens)
        if token.line_leading and token.value in THEOREM_COMMANDS
    ]
    for theorem_number, index in enumerate(theorem_indices):
        theorem = tokens[index]
        source_theorem = source_theorems[theorem_number]
        error_line = _line_number(source_text, source_theorem.start)
        error_context = _line_excerpt(source_text, source_theorem.start)
        limit = _next_outer_declaration(tokens, index + 1)
        candidate_index = None
        starter_index = None
        for current in range(index + 1, len(tokens)):
            token = tokens[current]
            if token.start >= limit:
                break
            if candidate_index is None and token.value in PROOF_PREFIXES:
                candidate_index = current
            if token.value in PROOF_STARTERS:
                starter_index = current
                break
        if starter_index is None:
            raise GenerationError(
                "theorem has no supported proof terminator",
                line=error_line,
                context=error_context,
            )

        proof_start_index = candidate_index if candidate_index is not None else starter_index
        proof_start = tokens[proof_start_index].start
        try:
            proof_end = _proof_end(text, masked, tokens, starter_index, limit)
        except GenerationError as error:
            if error.line is not None:
                raise
            raise GenerationError(
                str(error),
                line=error_line,
                context=error_context,
            ) from error
        indent_start = text.rfind("\n", 0, proof_start) + 1
        indent = text[indent_start:proof_start]
        if indent.strip():
            indent = " "
        replacements.append((proof_start, proof_end, "sorry"))

    for start, end, replacement in sorted(replacements, reverse=True):
        text = text[:start] + replacement + text[end:]
    return text


def generate_file(source: Path, output: Path) -> None:
    source_text = source.read_text(encoding="utf-8")
    generated = transform_theory(source_text, output.stem)
    output.parent.mkdir(parents=True, exist_ok=True)

    temporary_name: str | None = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="w",
            encoding="utf-8",
            newline="",
            dir=output.parent,
            prefix=f".{output.name}.",
            suffix=".tmp",
            delete=False,
        ) as temporary:
            temporary.write(generated)
            temporary.flush()
            os.fsync(temporary.fileno())
            temporary_name = temporary.name
        os.replace(temporary_name, output)
    except Exception:
        if temporary_name is not None:
            Path(temporary_name).unlink(missing_ok=True)
        raise


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path, help="source Isabelle theory")
    parser.add_argument("output", type=Path, help="generated proof-free theory")
    return parser


def main(argv: Iterable[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        generate_file(args.source, args.output)
    except (OSError, GenerationError) as error:
        print(f"generation failed: {error}", file=sys.stderr)
        return 1
    print(f"generated {args.output} from {args.source}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
