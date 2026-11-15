# Allocation-failure return sites (T1 obligation E, route (b): sizing)

Python tools used to size the whole-program table "every return from the allocator wrappers with a null
result ends in a `trap`" (`docs/bootstrap-target.md`, M1's later obligation). No proofs here.

- `dis.py`: a disassembler for `services/bootstrap/jam-bootstrap-service.jam` that follows `PVM/Instr.lean`'s
  `decode`/`skip`/`next`. `validate.py` checks it against the `d_N` facts in `Services/Bootstrap/Code*.lean`
  (0 mismatches over 21,507 facts on 2026-11-15). `python3 -I dis.py > dis.txt` regenerates the listing.
- `sites.py` → `sites.txt`: the call sites of `alloc` (40494) and `realloc` (40701).
- `explore.py`, `table.py` → `table.tsv`: each return site's class, trap pc and step count.
- `chains.py` → `chains.tsv`: the sites whose function passes `Err` to its caller, followed to the trap.

Result (2026-11-15): 32 return sites (28 alloc, 4 realloc). 24 trap within 2–4 instructions; 8 sit in 4
helpers (32989, 50146, 58327, 58717) whose callers trap at most 2 calls up, at most 30 instructions after the
failed allocation. No non-trapping site was found. Open: the SDK's finish_grow at 40852 (which calls the core
routine 41177 directly) and its callers 45036, 45251, 45767 are not traced yet.
