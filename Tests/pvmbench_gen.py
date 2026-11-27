"""Write a synthetic PVM program for `pvmbench`: a load/store/ALU loop of N iterations
(`loop.json`), or with an `ecalli` in every iteration (`loophost.json`, second argument `host`).
Usage: python3 Tests/pvmbench_gen.py N [host]"""
import json, sys
N = int(sys.argv[1]) if len(sys.argv) > 1 else 300000
HOST = len(sys.argv) > 2
OUT = 'loophost.json' if HOST else 'loop.json'
ins = []
def emit(*b): ins.append(list(b))
def le(x, n): return [(x >> (8*i)) & 255 for i in range(n)]
emit(51, 1, *le(0x20000, 3))          # r1 = 0x20000
emit(51, 2, *le(N, 3))                # r2 = N
emit(1)                               # fallthrough (terminator)
loop_idx = len(ins)
emit(130, 0x13)                       # r3 = u64 [r1]
emit(200, 0x23, 3)                    # r3 = r3 + r2
emit(132, 0x24, 0xF8, 0x7F)           # r4 = r2 & 0x7ff8
emit(200, 0x41, 5)                    # r5 = r1 + r4
emit(123, 0x53)                       # u64 [r5] = r3
emit(130, 0x56, 8)                    # r6 = u64 [r5 + 8]
emit(211, 0x63, 3)                    # r3 = r3 ^ r6
emit(59, 0x03, *le(0x30000, 3))       # u8 [0x30000] = r3
if HOST: emit(10, 0)                  # ecalli 0
emit(149, 0x22, 0xFF)                 # r2 = r2 - 1
br = len(ins); emit(82, 0x02, 0, 0)   # branch r2 != 0 -> loop (offset patched)
emit(50, 0x00)                        # jump_ind r0 (halt)
pos = []; p = 0
for b in ins: pos.append(p); p += len(b)
off = pos[loop_idx] - pos[br]
ins[br][2:4] = le(off & 0xFFFF, 2)
code = [x for b in ins for x in b]
mask = [0]*len(code)
for q in pos: mask[q] = 1
kb = []
for i in range(0, len(mask), 8):
    kb.append(sum(mask[i+j] << j for j in range(8) if i+j < len(mask)))
def encnat(x):
    assert x < 128
    return [x]
prog = encnat(0) + [0] + encnat(len(code)) + code + kb
json.dump({"name": "loop", "program": prog}, open(OUT, "w"))
print(len(code), prog)
