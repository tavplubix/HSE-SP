#!/usr/bin/env bash

set -e

rm -f fsm.txt fsm.txt.tests tests.out.log unit_tests.out.log mut_tests.out.log
rm -rf results

echo "Generating FSM, writing its description to fsm.txt"
./gen_fsm.py > fsm.txt

./curls.sh

echo -ne "Running tests:\t"
./run_tests.py fsm.txt.tests ./fsm_main.py > tests.out.log
echo -ne "OK\nLogs written to tests.out.log\n"

echo -ne "Running tests using unittest module:\t"
python3 -m unittest unit_test.py 2> unit_tests.out.log 1> unit_tests.out.log
echo -ne "OK\nLogs written to unit_tests.out.log\n"

echo -ne "Running mutation tests:\t"
mut.py --target fsm --unit-test unit_test -m -e > mut_tests.out.log
echo -ne "OK\nLogs written to mut_tests.out.log\n\n"

tail -6 mut_tests.out.log

echo -e "\nMoving all produced files to 'results/' dir"
mkdir results
mv fsm.txt fsm.txt.tests tests.out.log unit_tests.out.log mut_tests.out.log results/

