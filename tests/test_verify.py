import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import verify


class TestVerifiedMathFoundations(unittest.TestCase):
    def test_verify_coq_files(self):
        errors = verify.verify_coq_files()
        self.assertEqual(errors, [])


if __name__ == "__main__":
    unittest.main()
