

import LeanGrow.F.Prototypes.MarkFour.Search


open Lean


#check SearchState

def SolvedToOpenRatio (st : SearchState) : Float :=
  let conv := (st.back.id_gen_goal.toFloat)
  (st.back.id_gen_assign.toFloat) / (if conv == 0 then 1 else conv)


partial def BackTree.depth (bt : BackTree) : Nat :=
  let rec go (sofar : Nat) : List (BackTree × Nat) → Nat
    | [] => sofar
    | (nx,d) :: m =>
        match nx with
        | .fail | .ofAssign _ | .ofUni _ _ =>
          if d > sofar then go d m else go sofar m
        | .ofPropa _ _ _ _ _ as | .ofGoal _ _ _ _ as | .ofIntro _ _ _ _ _ as =>
          go sofar ((as.map (fun x => (x,d+1))) ++ m)
        | .ofBack _ _ _ _ as =>
          go sofar ((as.toList.map (fun x => (x,d+1))) ++ m)
  go 0 [(bt,0)]


partial def BackTree.width (bt : BackTree) : Nat :=
  let rec go (sofar : Nat) : List (BackTree) → Nat
    | [] => sofar
    | (nx) :: m =>
        match nx with
        | .fail | .ofAssign _ | .ofUni _ _ =>
          go sofar m
        | .ofPropa _ _ _ _ _ as | .ofGoal _ _ _ _ as | .ofIntro _ _ _ _ _ as =>
          let al := as.length
          if al > sofar then go al (as ++ m) else go sofar (as ++ m)
        | .ofBack _ _ _ _ as =>
          go sofar (as.toList ++ m)
          -- not here ; this would just favor using thms with many assumptions
          -- what we want to measure is the maximum number of alternatives
  go 1 [bt]


def DepthWidthCoefBack (widthFactor : Float) (st : SearchState) : Float :=
  let d := st.back.bt.depth.toFloat
  let w := st.back.bt.width.toFloat
  let prod := d * (widthFactor * w)
  let norm := d + (widthFactor * w)
  prod / norm
  -- should be largest if d ≈ w

--#exit

partial def ltx_depth (ltx_assemmbly : List (Nat × BackType × Array CExpr)) : Nat :=
  let rec go (sofar : Nat) (known : List (Nat × Nat)) : List (Nat × BackType × Array CExpr) → Nat
    | [] => sofar
    | (i,z, as) :: m =>
      match known.find? (fun x => x.1 == i) with
      | .some (_,d) => if d > sofar then go d known m else go sofar known m
      | _ =>
          let gidxs := as.foldl (fun L x =>
            match x with
            | .gnode idx _ => idx :: L
            | _ => L
            ) []
          let (ds,todos) := gidxs.foldl (fun (K1,K2) j =>
            match known.find? (fun x => x.1 == j) with
            | .some (_,D) => ((D) :: K1,K2)
            | _ => (K1, j :: K2)
            ) ([],[])
          match todos with
          | [] =>
              let current := (ds.foldl (fun S C => if C > S then C else S) 0) + 1
              if current > sofar then go current ((i,current) :: known) m else go sofar ((i,current) :: known) m
          | _ =>
            let (top, rest) := m.foldl (fun (T,R) x =>
              if todos.contains x.1 then (x :: T,R) else (T, x :: R)
              ) ([],[])
            go sofar known (top ++ ((i,z, as) :: rest))
  go 0 [] ltx_assemmbly



/-- largest number of times a gnode is an arguent to build another-/
partial def ltx_width (ltx_assemmbly : List (Nat × BackType × Array CExpr)) : Nat :=
  let rec go (known : List (Nat × Nat)) : List (Nat × BackType × Array CExpr) → List (Nat × Nat)
    | [] => known
    | (_,_,as) :: xs =>
        let gidxs := as.foldl (fun L x =>
            match x with
            | .gnode idx _ => idx :: L
            | _ => L
            ) []
        let rec new_known (done : List (Nat × Nat)) (gs : List Nat) : List (Nat × Nat) → List (Nat × Nat)
          | [] => (gs.map (fun x => (x,1))) ++ done
          | (i,deg) :: more =>
            if gs.isEmpty
            then done ++ more
            else
              if gs.contains i
              then new_known ((i,deg + 1):: done) (gs.erase i) more
              else new_known ((i,deg) :: done) gs more
        let new := new_known [] gidxs known
        go new xs
  let degs := go [] ltx_assemmbly
  degs.foldl (fun M (_,d) => if d > M then d else M) 0


def DepthWidthCoefForw (widthFactor : Float) (st : SearchState) : Float :=
  let d := (ltx_depth st.ltx_assemmbly).toFloat
  let w := (ltx_width st.ltx_assemmbly).toFloat
  let prod := d * (widthFactor * w)
  let norm := d + (widthFactor * w)
  prod / norm


/-

- Preciseness score: how many different cached states are triggered ? we want few ?
- Use ranking for parallelisation : give up on states that aren't well ranked ?

-/
