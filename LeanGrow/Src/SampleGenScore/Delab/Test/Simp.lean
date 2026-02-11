

import LeanGrow.Src.SampleGenScore.Delab.Simp

import Mathlib.Geometry.Convex.Cone.Basic

set_option linter.style.longLine false

open Lean Meta


def testSimpDelab (n : Name) : MetaM Unit := do
  let .some dec := (← getEnv).find? n | throwError "aaahhh"
  let cs ← mkPreProCongr
  lambdaTelescope dec.value! <| fun hyps p => do
    IO.println "TestH hyps"
    for h in hyps do
      IO.println s!" {← h.fvarId!.getUserName}: {← ppExpr (← h.fvarId!.getType)}"
    let .some l1 l2 res congrL extL nonTerm ← delab_simpGoal (← getLCtx) (← getLocalInstances) cs p [] #[] | IO.println "Simp not recognized"
    withLCtx l1 l2 <| do
      let res := cleanBetaTopTypes res
      -- ↑ and ↓↓ reverse the list, so we reverse it once more to get simply order
      let res := res.foldl .nil ListProd3.cons
      for (fvs,T,p) in res.toListOfProd do
        IO.println "\nStep stage:\nLifted (should be empty):"
        for h in fvs do
          IO.println s!" {← h.getUserName}: {← ppExpr (← h.getType)}"
        IO.println s!"Step stage:\n{← ppExpr T}"
        let _ ← (do match ← simpProof_topDelab_forTest p with
          | .some t =>
              let .some info := (← getEnv).find? t | pure ()
              IO.println s!"Theorem: {t}\nStatement: {← ppExpr info.type}"
          | _ =>
              IO.println s!"Printing raw: {p}")
      for L in congrL do
        IO.println "\nCongr-lift"
        let L := cleanBetaTopTypes L
        -- ↑ and ↓↓ reverse the list, so we reverse it once more to get simply order
        let L := L.foldl .nil ListProd3.cons
        for (fvs,T,p) in L.toListOfProd do
          -- let T := (T.instantiate hyps).headBeta -- β required for `ConvexCone.coe_iInf` for examlpe
          IO.println "\nStep stage:\nLifted:"
          for h in fvs do
            IO.println s!" {← h.getUserName}: {← ppExpr (← h.getType)}"
          IO.println s!"Step stage:\n{← ppExpr T}"
          let _ ← (do match ← simpProof_topDelab_forTest p with
            | .some t =>
                let .some info := (← getEnv).find? t | pure ()
                IO.println s!"Theorem: {t}\nStatement: {← ppExpr info.type}"
            | _ =>
                IO.println s!"Not const-headed, printing raw: {p}")
      for e in extL do
        IO.println s!"\nExternal-lift\nType {← ppExpr (← inferType e)}\nTerm {← ppExpr e}"
      IO.println s!"\nNonterminal:\n{← nonTerm.mapM ppExpr}"




-- tracing_mode .std
-- tracing_flags [(`delab_simpTheorem, [TracingFlags.zero]),
--                (`delab_simpCongrTheorem?, TracingFlags.all),
--                (`delab_simpStep, TracingFlags.all),
--                (`delab_simpStep.baseCase, TracingFlags.all),
--                (`delab_simpGoal, TracingFlags.all),
--                 ]


#print ConvexCone.pointed_iff_not_blunt
#eval testSimpDelab `ConvexCone.pointed_iff_not_blunt



#check ConvexCone.disjoint_coe._simp_1_1
#print ConvexCone.disjoint_coe
#eval testSimpDelab `ConvexCone.disjoint_coe


#print ConvexCone.subset_hull -- non rw
#eval testSimpDelab `ConvexCone.subset_hull


#print ConvexCone.coe_iInf
#eval testSimpDelab `ConvexCone.coe_iInf


#print ConvexCone.salient_positive
open ConvexCone in
def ConvexCone_salient_positive_simp
  {R : Type _} [Semiring R] [PartialOrder R]
  {G : Type _} [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G]
  [Module R G] [PosSMulMono R G]
  (x : G) (hx_nonneg : x ∈ positive R G) (hx_ne_zero : x ≠ 0) (hx_nonpos : -x ∈ positive R G)
  : 0 < 0 :=
    (Eq.mpr (id (lt_self_iff_false._simp_1 0))
      (False.elim
        (Eq.mp (Eq.trans (congrArg (LT.lt 0) (neg_add_cancel x)) (lt_self_iff_false._simp_1 0))
          (add_pos_of_nonneg_of_pos hx_nonpos (LE.le.lt_of_ne' hx_nonneg hx_ne_zero)))))

#eval testSimpDelab `ConvexCone_salient_positive_simp
-- duplication of lt_self_iff_false sample is not a bug : its present twice in the proof


#print Convex.mem_toCone
#eval testSimpDelab `Convex.mem_toCone


#check 1

#print List.reverse_cons
#eval testSimpDelab `List.reverse_cons

#check List.drop_eq_nil_of_le

open List
#check length_dropLast_cons

theorem test_1 {as : List Nat} {n : Nat} (h : as.length = n) : (42 :: as).dropLast.length = n := by
  simp
  rw [h]



#print test_1
#eval testSimpDelab `test_1


theorem test_2 {n : Nat} {tl : List α} (hn : n + 1 ≤ tl.length + 1)
  : n ∈ {n | n ≤ tl.length} := by
    simpa [Nat.succ_le_succ_iff] using hn

#print test_2
#eval testSimpDelab `test_2


#check 1

open List

theorem test_3_1 (α β : Type _) (l : List α) (p : β → Prop) (f : α → β)
   : Forall p (map f []) ↔ Forall (p ∘ f) [] := by
   simp [*]

#print test_3_1
-- #eval testSimpDelab `test_3_1


theorem test_3_2 (α β : Type _) (l : List α) (p : β → Prop) (f : α → β)
  (head : α) (tail : List α) (tail_ih : Forall p (map f tail) ↔ Forall (p ∘ f) tail)
  : Forall p (map f (head :: tail)) ↔ Forall (p ∘ f) (head :: tail) := by
   simp [*]

#print test_3_2


#eval testSimpDelab `test_3_2

open Function

open Nat
theorem test_4 {p : α → Prop} {f : ∀ a : α, p a → β} {s t : List α}
    (hs : ∀ a ∈ s, p a) (ht : ∀ a ∈ t, p a)
    (hf : ∀ (a a' : α) (ha : p a) (ha' : p a'), f a ha = f a' ha' → a = a')
    (h : Disjoint s t) :
    --Disjoint (s.pmap f hs) (t.pmap f ht) := by
    ∀ ⦃a : β⦄, a ∈ pmap f s hs → a ∈ pmap f t ht → False := by
      -- unfold List.Disjoint
      simp [mem_pmap]
      sorry

#print test_4
#print List.disjoint_pmap

tracing_mode .std
tracing_flags [(`delab_simpTheorem, [TracingFlags.zero]),
               (`delab_simpCongrTheorem?, TracingFlags.all),
               (`delab_simpStep, TracingFlags.all),
               (`delab_simpStep.baseCase, TracingFlags.all),
               (`delab_simpGoal, TracingFlags.all),
                ]

set_option pp.parens true
#eval testSimpDelab `test_4
