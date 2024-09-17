
import LeanGrow.Goal_Frontend_Mark1
--import LeanGrow.SampleSensitive
-- import conflicst :<
import LeanGrow.DAGstruct

open Lean Data Meta


def Expr.isSensitiveType (e : Expr) : MetaM Bool := do
  let T ← inferType e
  match T with
  | .sort .zero => return false
  | _ => return true


/-
Notes to self:

- We should have theorems as DAGs with CExpr, *with additionally* the goal as a CExpr with the right CExpr.node instead of the fvars
- Perform assignment by pattern matching, similarly to `Goal_Frontend_Mark1`
- In the DAG of hyps, replace nodes by matched expr (in node types) ; this require the CExpr type to allow for fvars, which may step from the context
  where the unification happend. (A proiri ... if I do a fronted where we switch to DAGs and CExpr from the start, this shouldn't be necessary ???)
  We will also have to mark the nodes that are given values via the assignement.
- to tell if a node has a sensitive type, we need to infer the Type of a CExpr ... either find some system
  to temporarily replace nodes by fvars and infer in that context, or make custom type inference algo ...
- To guess a value of a sensitively typed node that hasen't recieved a val through assignment, but who's type
  is fully assigned (= has no CExpr.node), we use the samples associated to the theorem we're applying.
- Here, we should do another unification, between (the type of) the argument used in the sample and the type from
  the dag node ...

Scenrio: suppose we may apply `by_cases`, as checked below. There, `q` gets assigned (and may contain fvar refering to
a Context if we keep fvars in our frontend) with the target goal. In the dag of the thm, we should then mark `q`s
node as assigned, and replace its value in the types of the sinks `hpq` and `hnpq`. Then `p` is the only node who's
type containes no nodes : since its a sensitive type, we will lookup samples to fill it with.
Now, if we find a sample of `by_cases`, for which the goal unifies with the target one, and hence also `q`, we consider
this sample further. The assignement may require giving some fvars of both the target theorem and that of the sample (recall
that samples and their goal have a Context), to be assignent special values wrt. each other. For example if the traget was
`x+2=3` for a fvar `x` and the sample has form `y=z` for fvars `y` and `z`, ... Note that here we should assign `y := x+2` and
leave `x` untouched, as it steps from the actual target.
So its a good idea to store the samples in a way that allows for each assignment of fvars, so possibly as a DAG too ???
Next, we consider the value used as argument for the sensitive type in the sample (which may have fvars from its own Context,
some of which may have been assigned from unifying the goals). For example, in our `by_cases` application, `p` may be given
value `n%2=0`, which is the value of the corresponding argument in the sample, where `n` refers to some number from the context
of the sample. Now, if we wish to use `n%2=0` as value for `p`, we need to assign meaning to `n` in the initial context that we're
actually working in. Note that `n` may not necessarily be liked to the goal of the sample (`y=z` in our example), but for the case
that it is, it should be assigned the coherent value from the previous assignement.
The easiest method to give meaning to `n` would be to look for a `Nat` in the initial context, or ask it to be queried in the
same way we're develloping, since it's a sensitive type.
Probably, the best way to handle this is to simply discard the sample or the theorem aplpication all together...
Now, if `n` is assigned meaning in the actual context, we may use `n%2=0` as value for `p`, and let `hpq` and `hnpq`
be the next goals to handle, since after replaceing the val of `p` in their type, they have no more nodes, and they
aren't sensitive types (aka. Props).

Note the interesting question of assigning `n` in the above. With our method, we would go over defs producing Nats, such as
`Nat.succ`. The argument to it should either be a Nat from context or a further generation of the sensitve type Nat.
Somehow, it would be good if samples stored information that would allow us to rank whether `Nat.succ` makes sense here


-/

#check by_cases


#exit

def helper_assign_3 (match_data : RBMap Nat Expr (instOrdNat.compare)) (thm_type : Expr) (thm_name : Name) (thm_lp : List Name) : MetaM (CExpr × List Expr) := do
  let assumptions := (helper_assign_1 thm_type)
  --dbg_trace s!"MD : {match_data.toList}"
  let (res, _) ← assumptions.foldlM (
    fun (e,c) (h) =>
      match match_data.find? c with
      | .some a => do return (.app e a, c-1)
      | _ => do
          let h' := helper_assign_0 match_data 0 (c+1) h
          if ← Expr.isSensitiveType h' -- should probably be done in the Context of the goal type, as match_data may contain free vraiables from that context
          then

          --let new_mv ← mkFreshExprMVar (.some (h')) ; Lean.MVarId.setType new_mv.mvarId! h'; return (.app e new_mv, c-1)
    ) ((Expr.const thm_name (thm_lp.map Level.param)), (assumptions.length-1))
  --dbg_trace s!"Output : {res}"
  return res
