#!/usr/bin/env python3

import sys
import fsm


if __name__ == "__main__":
    data = sys.stdin.read()
    res = fsm.get_fsm_output(data)
    sys.stdout.write(res)


