/-
  Round 10, member m1 (final report): the axiom audit of the round-9 kernel additions.

  This file prints the axiom sets of the headline theorems of the three round-9
  layers whose sources I re-elaborated in this directory in round 10:

    * MetzlerSharp.lean   (round 9, m9, direction d8): the dihedral obstruction
    * ACConj.lean         (round 9, m10, direction d10): the conjugator layer
    * ACPack.lean         (round 9, m8, direction L3): the packed closed-set layer

  Nothing here is new mathematics: it is the campaign's standard axiom audit,
  run by the report's author on the round-9 additions rather than inherited.
-/
import MetzlerSharp
import ACConj
import ACPack

#print axioms MetzlerSharp.abelian_metz_one
#print axioms MetzlerSharp.coprime_of_recipe_hypothesis
#print axioms MetzlerSharp.abelian_of_coprime
#print axioms MetzlerSharp.not_mulEquiv_four_even
#print axioms MetzlerSharp.not_mulEquiv_four_two_two

#print axioms ACConj.applyX_ac
#print axioms ACConj.runX_ac
#print axioms ACConj.conjL_length_ge
#print axioms ACConj.conjW_length_le
#print axioms ACConj.run_sim
#print axioms ACConj.run_sim_totLen_le
#print axioms ACConj.run_mem_of_closed
#print axioms ACConj.full_conj_mem_of_closed

#print axioms ACPack.bmem_bld
#print axioms ACPack.packCheck_sound
#print axioms ACPack.packCheckC_flatten
#print axioms ACPack.not_reach_of_facts
#print axioms ACPack.runPack_sound
