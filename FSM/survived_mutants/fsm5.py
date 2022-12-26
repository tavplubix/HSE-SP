#!/usr/bin/env python3


def get_fsm_output(fsm_input):
    look_for = 'ing '
    s = 0
    
    res = ''
    for c in fsm_input:
        o = '0'
        if c == look_for[s]:
            if s == 3:
                o = '1'
                s = 1
            else:
                s = s + 1
        elif c == look_for[0]:
            s = 1
        else:
            s = 0
        res += o

    return res


