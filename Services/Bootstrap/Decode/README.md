# Decode

- 2026-11-15 (T1, approved by the coordinator): `LoopAPassC.OkFD` no longer has the unused `es.length < 128` conjunct, so a decode batch may hold any number of elements (`OkF.toD` adjusted); this discharges `Refine/DecodeVecNC`'s former `hbatch`.
