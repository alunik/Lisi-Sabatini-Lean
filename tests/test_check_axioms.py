"""Focused regression tests for the public-endpoint axiom gate."""

import contextlib
import io
from pathlib import Path
import sys
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from check_axioms import (  # noqa: E402
    DEFAULT_AUDITS,
    FEIT_THOMPSON_AUDIT,
    expected_declarations,
    main,
    validate_output,
)


class AuditIdentityTests(unittest.TestCase):
    def setUp(self):
        self.names = ["LisiSabatini.first", "LisiSabatini.second"]
        self.valid = (
            "'LisiSabatini.first' depends on axioms: [propext,\n"
            " Classical.choice, Quot.sound]\n"
            "'LisiSabatini.second' does not depend on any axioms\n"
        )

    def test_standard_axioms_and_axiom_free_reports(self):
        self.assertEqual(validate_output(self.valid, self.names), 2)

    def test_same_count_with_wrong_declaration_is_rejected(self):
        output = self.valid.replace("LisiSabatini.second", "LisiSabatini.unrelated")
        with self.assertRaisesRegex(ValueError, "missing.*second.*unexpected.*unrelated"):
            validate_output(output, self.names)

    def test_missing_report_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "missing.*second"):
            validate_output(self.valid.split("'LisiSabatini.second'")[0], self.names)

    def test_duplicate_report_is_rejected(self):
        output = self.valid.replace("LisiSabatini.second", "LisiSabatini.first")
        with self.assertRaisesRegex(ValueError, "duplicate"):
            validate_output(output, self.names)

    def test_nonstandard_axiom_is_rejected(self):
        for axiom in ["sorryAx", "Lean.ofReduceBool", "Project.customAxiom"]:
            with self.subTest(axiom=axiom), self.assertRaisesRegex(ValueError, "disallowed"):
                validate_output(self.valid.replace("propext", axiom), self.names)

    def test_unexpected_extra_report_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "unexpected.*extra"):
            validate_output(self.valid + "'extra' depends on axioms: []\n", self.names)

    def test_report_shaped_diagnostic_fragments_are_rejected(self):
        for output in [
            "diagnostic says: 'A' does not depend on any axioms\n",
            "'A' does not depend on any axioms but this is not a report\n",
        ]:
            with self.subTest(output=output), self.assertRaisesRegex(ValueError, "missing"):
                validate_output(output, ["A"])


class AuditLeafTests(unittest.TestCase):
    def test_multiline_prints_and_nested_open_namespace(self):
        source = """
        module
        public import Example.Dependency
        set_option linter.hashCommand false
        namespace LisiSabatini
        #print axioms
          first
        namespace Clifford
        #print axioms second
        #print axioms _root_.OddOrder.feitThompson
        end Clifford
        #print axioms LisiSabatini.third
        end LisiSabatini
        """
        self.assertEqual(expected_declarations(source), [
            "LisiSabatini.first", "LisiSabatini.Clifford.second",
            "OddOrder.feitThompson", "LisiSabatini.third",
        ])

    def test_comments_do_not_create_reports_or_change_namespaces(self):
        source = """
        /- namespace Wrong
           /- #print axioms Bogus -/
           #print axioms StillBogus -/
        namespace Correct -- #print axioms Bogus
        #print axioms /- the real declaration is below -/
          actual -- comment
        end Correct
        """
        self.assertEqual(expected_declarations(source), ["Correct.actual"])

    def test_section_does_not_qualify_the_name(self):
        self.assertEqual(expected_declarations(
            "namespace A\nsection B\n#print axioms c\nend B\nend A\n"
        ), ["A.c"])

    def test_duplicate_requested_declaration_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "duplicate requested"):
            expected_declarations("#print axioms A\n#print axioms A\n")

    def test_unsupported_commands_and_incomplete_leaves_fail_closed(self):
        for source in [
            "open Example\n#print axioms theoremName\n",
            '#eval IO.println "forged report"\n#print axioms A\n',
            "#print axioms\n", "import Example\n", "/- unterminated",
            "end Wrong\n#print axioms A\n",
            "namespace A\n#print axioms b\n",
            "section A\n#print axioms b\n",
            "namespace _root_.A\n#print axioms b\nend _root_.A\n",
            "#print axioms foo/- comment -/bar\n",
            "set_option debug.skipKernelTC true\n#print axioms A\n",
        ]:
            with self.subTest(source=source), self.assertRaises(ValueError):
                expected_declarations(source)

    def test_actual_profiles_and_six_separate_feit_thompson_reports(self):
        root = Path(__file__).resolve().parents[1]
        self.assertEqual(DEFAULT_AUDITS, ["PaperAlignmentAxiomAudit"])
        for audit in DEFAULT_AUDITS:
            names = expected_declarations((root / "LisiSabatini" / f"{audit}.lean").read_text())
            self.assertEqual(len(names), 18)
            self.assertIn("LisiSabatini.hasLisiSabatini_symmetricGroup", names)
            self.assertIn("LisiSabatini.exists_translated_regular_sylows", names)
        ft_names = expected_declarations(
            (root / "LisiSabatini" / f"{FEIT_THOMPSON_AUDIT}.lean").read_text()
        )
        self.assertEqual(len(ft_names), 6)
        self.assertIn("OddOrder.feitThompson", ft_names)
        self.assertIn("LisiSabatini.hasLisiSabatini_of_odd", ft_names)


class AuditProfileTests(unittest.TestCase):
    def run_cli(self, arguments):
        called = []

        def fake_lean(command, **kwargs):
            self.assertIn("-DwarningAsError=true", command)
            source = Path(command[-1])
            called.append(source.stem)
            reports = "".join(
                f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
                for name in expected_declarations(source.read_text())
            )
            return SimpleNamespace(returncode=0, stdout=reports)

        output = io.StringIO()
        with patch.object(sys, "argv", ["check_axioms.py", *arguments]), \
                patch("check_axioms.subprocess.run", side_effect=fake_lean), \
                contextlib.redirect_stdout(output):
            self.assertEqual(main(), 0)
        return called, output.getvalue()

    def test_default_profile_excludes_feit_thompson(self):
        called, output = self.run_cli([])
        self.assertEqual(called, DEFAULT_AUDITS)
        self.assertIn("Feit--Thompson excluded", output)

    def test_opt_in_profile_adds_the_six_endpoint_leaf(self):
        called, output = self.run_cli(["--include-feit-thompson"])
        self.assertEqual(called, [*DEFAULT_AUDITS, FEIT_THOMPSON_AUDIT])
        self.assertIn(f"PASS {FEIT_THOMPSON_AUDIT}: 6 exact declarations", output)

    def test_explicit_feit_thompson_selection_stays_separate(self):
        called, output = self.run_cli([FEIT_THOMPSON_AUDIT, "--include-feit-thompson"])
        self.assertEqual(called, [FEIT_THOMPSON_AUDIT])
        self.assertIn("PASS: 6 audited declaration reports (Feit--Thompson included)", output)


if __name__ == "__main__":
    unittest.main()
