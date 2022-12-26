#!/usr/bin/env python3

from unittest import TestCase
import fsm
from run_tests import run_test

TESTS_FILE_NAME = 'fsm.txt.tests'


class FSMTest(TestCase):

    def test_fsm(self):
        f = open(TESTS_FILE_NAME, 'r')
        tests_data = f.read()
        f.close()
        tests_data = [line.strip() for line in tests_data.split('\n') if len(line.strip()) != 0]
        print("Will run {} tests from {}".format(len(tests_data), TESTS_FILE_NAME))

        for test_data in tests_data:
            test = [x.split('/') for x in test_data.split(' ')]
            test_in = ''.join([x[0] for x in test]).replace('_', ' ')
            expected = ''.join([x[1] for x in test])
            got = fsm.get_fsm_output(test_in)
            self.assertEqual(got, expected)


