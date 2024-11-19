
import LeanGrow.F.Utils.ExprTrieRW.Unify

open Lean

/-- should be used to build lnode matches, so that we can propagate ;
Recall that this builds the type, not the term of that type
-/
partial def rwExpr.toCExpr (rww : rwExpr α) : CExpr :=
  let rec go : List (rwExpr α) → List CExpr
    | [] => []
    | nx :: more =>
        match nx with
        | .ofAtom ce => ce :: (go more)
        | .wRW _ _ _ ce => go (ce :: more)
        | .app f a =>
            let r := go (f :: a :: more)
            let (F,r2) := List.headD_tail r .failed
            let (A,r3) := List.headD_tail r2 .failed
            (.app F A) :: r3
        | .lam n f a i =>
            let r := go (f :: a :: more)
            let (F,r2) := List.headD_tail r .failed
            let (A,r3) := List.headD_tail r2 .failed
            (.lam n F A i) :: r3
        | .forallE n f a i =>
            let r := go (f :: a :: more)
            let (F,r2) := List.headD_tail r .failed
            let (A,r3) := List.headD_tail r2 .failed
            (.forallE n F A i) :: r3
        | .letE n f a z i =>
            let r := go (f :: a :: z :: more)
            let (F,r2) := List.headD_tail r .failed
            let (A,r3) := List.headD_tail r2 .failed
            let (Z,r4) := List.headD_tail r3 .failed
            (.letE n F A Z i) :: r4
        | .proj n i f =>
            let r := go (f :: more)
            let (F,r2) := List.headD_tail r .failed
            (.proj n i F) :: r2
  List.headD (go [rww]) .failed


partial def CExpr.buildRWofRwExpr
      (fctx : FixCtx)
      (classes : List (Nat × RWClassData))
      (mainData : List (Nat × CExpr)) -- gnodes with type
      (BP : rwExpr Nat) : CExpr :=


      -- let rec go (term type Ttype : CExpr) : List (List rwDirs × RWblueprint Nat) → CExpr
      -- | [] => term
      -- | (dirs, bp) :: more =>
      --       match bp with
      --       | .exactMatch classId entryId ind =>
      --             match classId, entryId with
      --             | .none, _ => .failed
      --             | .some cId, .some eId =>
      --                   match classes.find? (fun x => x.1 == cId) with
      --                   | .none => .failed
      --                   | .some (_, cData) =>
      --                         match ind.head? with
      --                         | .none => .failed
      --                         | .some I =>
      --                               match cData.class_cexprs.find? (fun x => x.1 == I) with
      --                               | .some (_,ce) => -- the term corresponding to eId should be that that will get factored
      --                                     --let Ttype := CExpr.whnf fctx (CExpr.inferType fctx type) -- can it change durring rws ? if not, store it as param
      --                                     let (motive, ceE) := CExpr.factor type dirs Ttype
      --                                     let inClass := buildEqThm cData.class_type cData.class_type_level cData.class_cexprs cData.base cData.class_graph eId I
      --                                     let motiveType := CExpr.inferType fctx motive
      --                                     match Ttype, motiveType with -- level of Ttype should be param
      --                                     | .sort u2, .forallE _ _ (.sort u1) _ =>
      --                                           let rwed := CExpr.mkApp (.const `Eq.ndrec [u1,u2]) [Ttype, ceE, motive, type, ce, inClass]
      --                                           let nweType := CExpr.whnf fctx (.app motive ce)
      --                                           go rwed nweType Ttype more
      --                                     | _, _ => .failed
      --                               | _ => .failed
      --             | _, _ => .failed
      --       | .node classId entryId ind ndirs chi =>
      --             match classId, entryId with
      --             | .some cId, .some eId =>
      --                   match classes.find? (fun x => x.1 == cId) with
      --                   | .none => .failed
      --                   | .some (_, cData) =>
      --                         match ind.head? with
      --                         | .none => .failed
      --                         | .some I =>
      --                               match cData.class_cexprs.find? (fun x => x.1 == I) with
      --                               | .none => .failed
      --                               | .some (_,ce) =>
      --                                     let (motive, ceE) := CExpr.factor type dirs Ttype
      --                                     let inClass := buildEqThm cData.class_type cData.class_type_level cData.class_cexprs cData.base cData.class_graph eId I
      --                                     let motiveType := CExpr.inferType fctx motive
      --                                     match Ttype, motiveType with -- level of Ttype should be param
      --                                     | .sort u2, .forallE _ _ (.sort u1) _ =>
      --                                           let rwed := CExpr.mkApp (.const `Eq.ndrec [u1,u2]) [Ttype, ceE, motive, type, ce, inClass]
      --                                           let nweType := CExpr.whnf fctx (.app motive ce)
      --                                           let todos := List.zipWith (fun d bp => (dirs ++ d.2.2, bp)) ndirs chi
      --                                           go rwed nweType Ttype (todos ++ more)
      --                                     | _, _ => .failed
      --             | _, _ => .failed -- none is expected to be handled before calls to go
      -- match BP with
      -- | .exactMatch .none .none ind =>
      --       match ind.head? with
      --       | .none => .failed
      --       | .some I => .gnode I (.ofBvar 42)
      -- | .node .none .none ind ndirs chi =>
      --       match ind.head? with
      --       | .none => .failed
      --       | .some I =>
      --             match mainData.find? (fun x => x.1 == I) with
      --             | .none => .failed
      --             | .some (_,ce) =>
      --                   let Ttype := CExpr.whnf fctx (CExpr.inferType fctx ce)
      --                   let todos := List.zipWith (fun d bp => (d.2.2, bp)) ndirs chi
      --                   go (.gnode I (.ofBvar 42)) ce Ttype todos
      -- | _ => .failed
