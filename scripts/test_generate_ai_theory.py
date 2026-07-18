from __future__ import annotations

import sys
import tempfile
import textwrap
import unittest
from pathlib import Path


sys.path.insert(0, str(Path(__file__).resolve().parent))

from generate_ai_theory import GenerationError, generate_file, transform_theory


def theory(body: str) -> str:
    return "theory Source\n  imports Main\n\nbegin\n\n" + textwrap.dedent(body) + "\nend\n"


class TransformTheoryTests(unittest.TestCase):
    def transform(self, body: str) -> str:
        return transform_theory(theory(body), "Skeleton")

    def test_one_line_by_proof(self) -> None:
        result = self.transform('lemma example: "P" by simp')
        self.assertIn('lemma example: "P" sorry', result)
        self.assertNotIn("by simp", result)

    def test_structured_proof(self) -> None:
        result = self.transform(
            '''
            lemma example:
              "P"
            proof -
              show P sorry
            qed
            '''
        )
        self.assertIn('lemma example:\n  "P"\nsorry', result)
        self.assertNotIn("proof", result)
        self.assertNotIn("qed", result)

    def test_nested_structured_proofs(self) -> None:
        result = self.transform(
            '''
            lemma nested:
              "P"
            proof -
              have "Q"
              proof -
                show Q sorry
              qed
              show P sorry
            qed
            lemma after: "R" by simp
            '''
        )
        self.assertEqual(result.count("sorry"), 2)
        self.assertIn('lemma after: "R" sorry', result)
        self.assertNotIn("have", result)

    def test_apply_done_proof(self) -> None:
        result = self.transform(
            '''
            lemma example:
              "P"
              apply simp
              done
            '''
        )
        self.assertIn('lemma example:\n  "P"\n  sorry', result)
        self.assertNotIn("apply", result)
        self.assertNotIn("done", result)

    def test_apply_proof_terminated_by_by(self) -> None:
        result = self.transform(
            '''
            lemma example:
              "P"
              apply simp
              by auto
            '''
        )
        self.assertIn('lemma example:\n  "P"\n  sorry', result)
        self.assertNotIn("apply", result)
        self.assertNotIn("by auto", result)

    def test_assumptions_and_shows_are_preserved(self) -> None:
        result = self.transform(
            '''
            lemma implication:
              assumes first: "P"
              and second: "Q"
              shows "R"
              using first second
              unfolding some_definition
              by auto
            '''
        )
        self.assertIn('assumes first: "P"', result)
        self.assertIn('and second: "Q"', result)
        self.assertIn('shows "R"', result)
        self.assertNotIn("using first", result)
        self.assertNotIn("unfolding some_definition", result)

    def test_fixes_assumes_and_defines_are_preserved(self) -> None:
        result = self.transform(
            '''
            theorem configured[attrib]:
              fixes x :: nat
              assumes positive: "x > 0"
              defines "y \u2261 x + 1"
              shows "y > 0"
              by simp
            '''
        )
        self.assertIn("theorem configured[attrib]:", result)
        self.assertIn("fixes x :: nat", result)
        self.assertIn('assumes positive: "x > 0"', result)
        self.assertIn('defines "y \u2261 x + 1"', result)
        self.assertIn('shows "y > 0"', result)

    def test_comments_are_removed_but_definitions_and_functions_remain(self) -> None:
        body = '''
            (* A declaration comment. *)
            definition proof_label :: string where
              "proof_label = ''proof by qed''"

            fun identity :: "nat \u21d2 nat" where
              "identity n = n"

            lemma identity_rule: "identity n = n" by simp
        '''
        result = self.transform(body)
        self.assertNotIn("A declaration comment", result)
        self.assertIn('"proof_label = \'\'proof by qed\'\'"', result)
        self.assertIn('"identity n = n"', result)

    def test_multiple_consecutive_theorems_and_kinds(self) -> None:
        result = self.transform(
            '''
            lemma one: "A" by simp
            theorem two: "B" by simp
            proposition three: "C" by simp
            corollary four: "D" by simp
            '''
        )
        self.assertEqual(result.count("sorry"), 4)
        for name in ("one", "two", "three", "four"):
            self.assertIn(name, result)

    def test_proof_words_in_strings_comments_and_cartouches_are_ignored(self) -> None:
        result = self.transform(
            '''
            (* proof qed by apply done, including (* nested proof *) *)
            definition message :: string where
              "message = ''proof qed by''"
            abbreviation cartouche_text where
              "cartouche_text \u2261 \u2039proof qed by\u203a"
            lemma safe: "message = message" (* by proof qed *) by simp
            '''
        )
        self.assertNotIn("nested proof", result)
        self.assertIn("''proof qed by''", result)
        self.assertIn("\u2039proof qed by\u203a", result)
        self.assertEqual(result.count("sorry"), 1)

    def test_comments_inside_proof_are_removed(self) -> None:
        result = self.transform(
            '''
            lemma example: "P"
            proof -
              (* proof-only explanation *)
              show P sorry
            qed
            (* Comment for the next declaration. *)
            lemma next: "Q" by simp
            '''
        )
        self.assertNotIn("proof-only explanation", result)
        self.assertNotIn("Comment for the next declaration", result)

    def test_multiline_and_inline_comments_are_compacted_safely(self) -> None:
        result = self.transform(
            '''
            (* A standalone comment
               spanning several lines. *)
            datatype side = Left (* nested (* detail *) text *) | Right
            definition message :: string where
              "message = ''(* string content *)''"
            abbreviation cartouche_text where
              "cartouche_text ≡ ‹(* cartouche content *)›"
            lemma safe: "Left ≠ Right" (* explanation *) by simp
            '''
        )
        self.assertNotIn("standalone comment", result)
        self.assertNotIn("nested (* detail *) text", result)
        self.assertIn("datatype side = Left  | Right", result)
        self.assertIn("''(* string content *)''", result)
        self.assertIn("‹(* cartouche content *)›", result)
        self.assertIn('lemma safe: "Left ≠ Right"  sorry', result)

    def test_malformed_literals_and_proofs_fail(self) -> None:
        with self.assertRaises(GenerationError):
            transform_theory('theory Bad imports Main begin lemma x: "P\n', "Out")
        with self.assertRaises(GenerationError):
            self.transform('lemma x: "P"\nproof -\n  show P sorry')
        with self.assertRaises(GenerationError):
            self.transform('lemma x: "P"\n  apply simp')


class AtomicGenerationTests(unittest.TestCase):
    def test_failed_generation_does_not_replace_existing_output(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "Broken.thy"
            output = root / "Skeleton.thy"
            source.write_text('theory Broken imports Main begin\nlemma x: "P"\nproof -\n', encoding="utf-8")
            output.write_text("existing output\n", encoding="utf-8")

            with self.assertRaises(GenerationError):
                generate_file(source, output)

            self.assertEqual(output.read_text(encoding="utf-8"), "existing output\n")
            self.assertEqual(list(root.glob(".Skeleton.thy.*.tmp")), [])

    def test_successful_generation_uses_output_filename_as_theory_name(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "Source.thy"
            output = root / "Generated_Context.thy"
            source.write_text(theory('lemma x: "P" by simp'), encoding="utf-8")
            generate_file(source, output)
            result = output.read_text(encoding="utf-8")
            self.assertTrue(result.startswith("theory Generated_Context\n"))


if __name__ == "__main__":
    unittest.main()
