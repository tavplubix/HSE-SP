#!/usr/bin/env python3

import sys
import subprocess


def run_test(test_data, i=None):
    test = [x.split('/') for x in test_data.split(' ')]
    test_in = ''.join([x[0] for x in test]).replace('_', ' ').encode()
    expected = ''.join([x[1] for x in test]).encode()
    if i is not None:
        print('Running test {}: "{}", expecting "{}"... '.format(i, test_in, expected), end='')
    got = subprocess.run([fsm_exec_name,], input=test_in, stdout=subprocess.PIPE).stdout
    if expected == got:
        if i is not None:
            print('OK')
    else:
        if i is not None:
            print('got "{}"'.format(got))
        raise Exception('Test "{}" failed: expected "{}", got "{}". Test parsed from "{}"'.format(test_in, expected, got, test_data))


if __name__ == "__main__":
    tests_file_name = sys.argv[1]
    fsm_exec_name = sys.argv[2]

    tests_data = open(tests_file_name, 'r').read()
    tests_data = [line.strip() for line in tests_data.split('\n') if len(line.strip()) != 0]

    print("Will run {} tests from {} for {}".format(len(tests_data), tests_file_name, fsm_exec_name))

    for i in range(0, len(tests_data)):
        run_test(tests_data[i], i)

    print("All tests pass")

