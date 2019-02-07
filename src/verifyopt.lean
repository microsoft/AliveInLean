-- Copyright (c) Microsoft Corporation. All rights reserved.
-- Licensed under the MIT license.

import .ops
import .lang
import .irsem

namespace opt
section

open irsem

parameter (sem : irsem)

-- uint_like types
variable [ihc:has_comp sem.intty sem.boolty]
variable [ioc:has_overflow_check sem.intty sem.boolty]
variable [iul:uint_like sem.intty]
-- poison types
variable [pbl:bool_like sem.poisonty]
variable [p2b:has_coe sem.poisonty sem.boolty]
-- bool types
variable [bbl:bool_like sem.boolty]
variable [b2i:has_coe sem.boolty (sem.intty size.one)]
variable [bhi:Π (sz:size), has_ite sem.boolty (sem.intty sz)]
variable [bhi2:has_ite sem.boolty sem.poisonty]

include ihc
include ioc
include iul
include bbl
include pbl
include p2b
include b2i
include bhi
include bhi2

def check_val (vsrc vtgt:irsem.valty sem) : option sem.boolty :=
  match vsrc, vtgt with
  | irsem.valty.ival sz1 v1 p1, irsem.valty.ival sz2 v2 p2 :=
    if H:sz1 = sz2 then
      some ((~ p1) |b (p2 & (v1 =_{sem.boolty} (cast (by rw H) v2))))
    else none
  end

def check_single_reg0 (psrc ptgt:program) (r:string) (initst:irstate sem) : option sem.boolty :=
  do
  s1 ← irsem.bigstep sem initst psrc,
  s2 ← irsem.bigstep sem initst ptgt,
  v1 ← irsem.irstate.getreg sem s1 r,
  v2 ← irsem.irstate.getreg sem s2 r,
  ref ← check_val v1 v2,
  return ((~ irstate.getub sem s1) |b (irstate.getub sem s2 & ref))

-- This is another version of check_single_reg0 that allows using variables
-- in the source instructions.
-- Currently, proof in AliveInLean does not exploit SSA property of a program, so this is
-- okay. regfile.update_get_match at spec/irstate.lean states that
-- the latest update to a variable has the latest value.
def check_single_reg (psrc ptgt:program) (r:string) (initst:irstate sem) : option sem.boolty :=
  do
  s1 ← irsem.bigstep sem initst psrc,
  s2 ← irsem.bigstep sem initst { insts := psrc.insts ++ ptgt.insts },
  v1 ← irsem.irstate.getreg sem s1 r,
  v2 ← irsem.irstate.getreg sem s2 r,
  ref ← check_val v1 v2,
  return ((~ irstate.getub sem s1) |b (irstate.getub sem s2 & ref))

end
end opt
