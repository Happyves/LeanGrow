
import LeanGrow.F.Utils.DAG.Types


-- # Dummies

def CExpr : Type := sorry




-- # State

structure ForwardState where
  cexprs : sorry -- store hyps and derived facts ; probably a discrimination tree is best
  deps : pDAG sorry sorry -- same as ↑, but store dependenices : which fact was derived from which hyps ; use dag notion that is easily extensible
  fakes : sorry -- if a thm was applied backwards, and its subgoal is ∀, we should introduce the ∀ hyps to the forward-state, but track them with this field, so as to know that they may only be sed to prove a specific subgoal
  rankings : sorry -- should link to another structure storing the rankings of the curretly derived facts


structure BackwardState where
  cexprs : sorry -- store goal ; probably a discrimination tree is best
  inner_deps : sorry -- should store a list of dags that represent depedndecies among goals
  polyutility : sorry-- to handle the fact that multiple goals may be the same, up to different CExpr-nodes, we use this field to manage this ; refer to note 3
  global_deps : sorry -- should be used to handle whish subgoals are considered as solved ; refer to note 2
  rankings : sorry

structure TriggerState where
  algebra : sorry
  SAT : sorry

structure SpecialSupportState where
  todo : sorry

structure SearchState where
  forward : ForwardState
  backward : BackwardState
  trigger : TriggerState
  spesup : SpecialSupportState
  tech : sorry -- decide on whether to make forward or backward step or both; maybe to manage when to do stuff as new `Task`s ?
  learning : sorry -- should store/manage datat for RL when we train grow ; add option to turn modfications this off for performance

/-
**Notes**

1.  Even if we apply a theorem that does't require sesnitive types as args, we may get dependecies:
    for example, assume we apply a thm that requires `(h₁ : n < 42)` and `(h₂ : List.get L ⟨n,h₁⟩ = 37)` ;
    the types aren't sensitve, yet `h₂` will depend on `h₁`

2.  We get the goal from a foward fact, or we get it backwards by having all child-goals solved.
    Perhaps this strutcure should also handle the order of goals ? Remeber that we wish to temporarily
    ignore goals related to a postulated sensitive type, and only start solving them once we know
    the proof works out with that sensitive type.

3.  The field should store a management structure that relates the node in the expression to those that actually
    correspond to concrete objects. For the purpose of ranking, maybe we can store sub-goal expressions as
    setTrie ? Then top nodes corespond by subgols requesed by many backward thms.



**More**

- For thms used backward, that have subgoals that contains ∀, we want to produce two subgoals for each of these
  ∀ subgoals : one where the terms are introduced as fake hyps in the forward state, and one where we leave the goal
  untouched. keeping the second only makes sense if forward can produce ∀ types.

-/
