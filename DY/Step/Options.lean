module

public import Lean

public
register_option step.admitMono : Bool := {
  defValue := false
  descr    := "(step) admit context monotonization proofs, for faster interactive mode"
}
