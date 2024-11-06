
import LeanGrow.F.Data.Unification.EmbedGoalWInfer


#check 1

def OptionInfo : CstInfo := .noVal [`u] (.sort 1)
def OptionMapInfo : CstInfo := .noVal [`u_1,`u_2]
    (.forallE `α (.sort (.param `u_1))
        (.forallE `β (.sort (.param `u_1))
            (.forallE `f (.forallE `x (.bvar 1) (.bvar 0) .default)
                (.forallE `arg (.app (.const `Option [.param `u_1]) (.bvar 1))
                  (.app (.const `Option [.param `u_2]) (.bvar 0))
                .default)
            .default)
        .implicit)
    .implicit)
def NoneInfo : CstInfo := .noVal [`u] (.forallE `x (.sort (.param `u)) (.app (.const `Option [.param `u]) (.bvar 0)) .default)
def NatInfo : CstInfo := .noVal [] (.sort 1)
def EqInfo : CstInfo := .noVal [`u] (.forallE `α (.sort (.param `u)) (.forallE `left (.bvar 0) (.forallE `right (.bvar 1) (.sort 0) .default) .default) .implicit)

#check Eq


lemma testThm {α : Type _} {β : Type _} (f : α → β) : Option.map f .none = .none := rfl

def fackCstData : CTrie CstInfo := CTrie.ofList
  [("Option", OptionInfo), ("Option.map", OptionMapInfo),
  ("Option.none", NoneInfo), ("Nat", NatInfo), ("Eq", EqInfo)]



def fakeThm : Array EmbedData :=
  #[.nonInst (.sort (.param `u_1)) #[] #[2],
    .nonInst (.sort (.param `u_2)) #[] #[2],
    .nonInst (.forallE `x (.lnode 0 (.ofBvar 1) .none) (.lnode 1 (.ofBvar 0) .none) .default) #[0,1] #[]
   ]

def fakeThmGoal : CExpr :=
  .app (
    .app
        (.app (.const `Eq [.param `u_2]) (.app (.const `Option [.param `u_2])  (.lnode 1 (.ofBvar 1) .none)))
        (.app (.app (.const `Option.map [.param `u_1, .param `u_2]) (.lnode 2 (.ofBvar 0) .none)) (.app (.const `Option.none [.param `u_1]) (.lnode 0 (.ofBvar 2) .none)))
    )
    (
     (.app (.const `Option.none [.param `u_2]) (.lnode 1 (.ofBvar 2) .none))
    )


def fakeGoal : CExpr :=
  .app (
    .app
        (.app (.const `Eq []) (.app (.const `Option [1]) (.const `Nat [])))
        (.app (.app (.const `Option.map [1,1]) (.lam `x (.const `Nat []) (.bvar 0) .default)) (.app (.const `Option.none [1]) (.const `Nat [])))
    )
    (
     (.app (.const `Option.none [1]) (.const `Nat []))
    )

def fakeFixCtx : FixCtx where
  gnodeTypes := []
  gnodeTypesHandler := fun _ => (0,0)
  ltxTypes := []
  current := .some fakeThm
  cstData := fackCstData

#check Option.map
#check Option Nat


#eval match_goal fakeFixCtx fakeThm 3 fakeThmGoal fakeGoal
