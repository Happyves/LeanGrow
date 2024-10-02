
import Lean

open Lean

def goal_data : Type := sorry

structure Trigger (trigger_state  : Type _) where
  state : trigger_state
  forward_transition : (trigger_state × LocalContext × goal_data) → sorry → (trigger_state × LocalContext × goal_data)
  backward_transition : (trigger_state × LocalContext × goal_data)  → sorry → (trigger_state × LocalContext × goal_data)
  run : sorry
