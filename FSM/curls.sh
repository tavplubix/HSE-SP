#!/usr/bin/env bash

FSM="fsm.txt"

INPUT="${RANDOM}_$FSM"
METHOD="black_box/w"
M="4"

set -e

echo -ne "Uploading $FSM as $INPUT:\t"
curl -s -F "file=@$FSM;filename=$INPUT" "http://fsmtestonline.ru/upload"
echo ""

echo -ne "\nValidating:\t"
curl -s "http://fsmtestonline.ru/validate_fsm?input_file=${INPUT}" | jq -re ".errors // empty" && exit 1 || echo OK

echo -ne "\nIs deterministic:\t"
curl -s "http://fsmtestonline.ru/is_deterministic?input_file=${INPUT}_conv" | jq -re ".message // empty" && exit 1 || echo OK

echo -ne "\nIs fully defined:\t"
curl -s "http://fsmtestonline.ru/is_fully_defined?input_file=${INPUT}_conv" | jq -re ".message // empty" && exit 1 || echo OK

echo -ne "\nIs connected:\t"
curl -s "http://fsmtestonline.ru/is_connected?input_file=${INPUT}_conv" | jq -re ".message // empty" && exit 1 || echo OK

echo -ne "\nIs reduced:\t"
curl -s "http://fsmtestonline.ru/is_reduced?input_file=${INPUT}_conv" | jq -re ".message // empty" && exit 1 || echo OK

echo -ne "\nNum states:\t"
curl -s "http://fsmtestonline.ru/num_states?input_file=${INPUT}_conv&fsm_desc=${INPUT}_desk" | jq -re ".states // empty"

echo -ne "\nGen tests with m=$M:\t"
curl -s "http://fsmtestonline.ru/$METHOD?input_file=${INPUT}_conv&fsm_desc=${INPUT}_desk&m=$M" | jq -re ".test" | sed "s/<br>/\n/g" > "$FSM.tests"
echo -e "See tests in '$FSM.tests'"

