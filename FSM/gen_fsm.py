#!/usr/bin/env python3

alphabet = [chr(ord('a') + i) for i in range(0, ord('z') - ord('a') + 1)]
alphabet += '_'

states = ['BEGIN', 'I', 'N', 'G']

out = ['0', '1']

print('F o')
print('s', len(states),   ' '.join(states))
print('i', len(alphabet), ' '.join(alphabet))
print('o', len(out),      ' '.join(out))
print('n0', states[0])
print('p', len(states) * len(alphabet))

special_chars = ['i', 'n', 'g', '_']
special_chars_out = ['0', '0', '0', '1']

for i in range(0, len(states)):
    s = states[i]
    c = special_chars[i]
    ns = states[(i + 1) % len(states)]
    s0 = states[0]
    o = special_chars_out[i]
    for a in alphabet:
        if a == special_chars[0]:
            print(s, a, states[1], '0')
        elif a == c:
            print(s, a, ns, o)
        else:
            print(s, a, s0, '0')


