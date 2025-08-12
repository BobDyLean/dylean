namespace Chamelean

axiom Bytes: Type 0

inductive Trace.Entry (a:Type) where
  | rand_gen: a -> Trace.Entry a
  | send_msg: Bytes -> Trace.Entry a
  | log_event: Trace.Entry a
  -- TODO

inductive Trace (a:Type) where
  | nil: Trace a
  | snoc: Trace a -> Trace.Entry a -> Trace a


namespace Trace

def Entry.map
  (f: a -> b) (e: Entry a)
  : Entry b
  :=
  match e with
  | .rand_gen pf => .rand_gen (f pf)
  | .send_msg msg => .send_msg msg
  | .log_event => .log_event

def Trace.map
  (f: a -> b) (tr: Trace a)
  : Trace b
  :=
  match tr with
  | .nil => .nil
  | .snoc tr_before e => .snoc (Trace.map f tr_before) (Entry.map f e)

instance : Functor Trace where
  map := Trace.map

instance : LawfulFunctor Trace where
  map_const := by
    intros
    simp [Functor.mapConst, Functor.map]
  id_map := by
    intros α tr
    simp [Functor.map]
    induction tr with
    | nil =>
      simp [Trace.map]
    | snoc tr_before e =>
      simp [Trace.map, Entry.map]
      grind
  comp_map := by
    intros α β γ g h tr
    simp [Functor.map]
    induction tr with
    | nil =>
      simp [Trace.map]
    | snoc tr_before e =>
      simp [Trace.map, Entry.map]
      grind

inductive LETrace : Trace a -> Trace a -> Prop where
  | equal: (tr: Trace a) -> LETrace tr tr
  | extend: (tr1: Trace a) -> (tr2: Trace a) -> (e: Entry a) -> LETrace tr1 tr2 -> LETrace tr1 (.snoc tr2 e)

instance : LE (Trace a) where
  le := LETrace

theorem trace_le_trans
  (tr1: Trace a) (tr2: Trace a) (tr3: Trace a)
  : tr1 ≤ tr2 → tr2 ≤ tr3 → tr1 ≤ tr3
  := by
    intros hxy hyz
    induction hyz with
    | equal => simp_all
    | extend tr3 e _ ih =>
      exact (LETrace.extend tr1 tr3 e ih)

-- grind_pattern trace_le_trans => tr1 ≤ tr2, tr1 ≤ tr3

instance : Trans (· ≤ · : Trace a → Trace a → Prop) (· ≤ ·) (· ≤ ·) where
  trans := by
    intros x y z
    exact trace_le_trans x y z
  /-by
    intros x y z hxy hyz
    induction hyz with
    | equal => simp_all
    | extend e _ ih =>
      exact (LETrace.extend e ih)
      -/

end Chamelean.Trace
