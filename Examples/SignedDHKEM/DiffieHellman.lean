module

public import DY.Bytes
public import DY.Trace
public import DY.Misc.Instances
public import DY.Trace.Manipulation -- HoareTriplePure
public import DY.Actions.ProtocolEvent
public import DY.Actions.Network
public import DY.Meta

namespace DY.DiffieHellman'

public
class CanDH (Bytes: Type u) where
  dhPk: (sk: Bytes) → Bytes
  dh: (pk: Bytes) → (sk: Bytes) → Bytes

export CanDH (dhPk)
export CanDH (dh)

section Constructors

namespace DhPk

public
structure BytesPart.Functor (Bytes: Type) where
  sk: Bytes

public
instance: ALaCarte.FunctorSizeOf BytesPart.Functor where
  sizeOf | {sk} => sizeOf sk

public
instance: ALaCarte.Representable BytesPart.Functor where
  CtorId := Unit
  ctors | () => { Data := Unit, nRec := 1 }

  toRepr | {sk} => {
    id := ()
    data := ()
    as := #v[sk]
  }
  fromRepr
  | {id, data, as} =>
    let sk := as[0]
    { sk }
  from_to | {sk} => by rfl
  to_from
  | {id, data, as} => by
    simp_all <;> grind
  sizeOf_eq | {sk} => by simp +arith [ALaCarte.FunctorSizeOf.sizeOf]

public instance: ALaCarte.RepresentableDecidableEq BytesPart.Functor where
public instance: ALaCarte.RepresentableOrd BytesPart.Functor where
public instance: Bytes.Part BytesPart.Functor where

public
def BytesPart.length [Bytes.Def]: Bytes.length.Part BytesPart.Functor :=
  fun _ _ =>
    32

-- workaround for lean4#11708
theorem BytesPart.Functor.sizeOf_eq
  [Bytes.Def]
  (x: BytesView BytesPart.Functor)
  : DY.ALaCarte.FunctorSizeOf.sizeOf x = sizeOf x.sk
:= by
  cases x
  simp [DY.ALaCarte.FunctorSizeOf.sizeOf]

grind_pattern BytesPart.Functor.sizeOf_eq => DY.ALaCarte.FunctorSizeOf.sizeOf x

end DhPk

namespace Dh

public
structure BytesPart.Functor (Bytes: Type) where
  pk: Bytes
  sk: Bytes

public
instance: ALaCarte.FunctorSizeOf BytesPart.Functor where
  sizeOf | {pk, sk} => sizeOf pk + sizeOf sk

public
instance: ALaCarte.Representable BytesPart.Functor where
  CtorId := Unit
  ctors | () => { Data := Unit, nRec := 2 }

  toRepr | {pk, sk} => {
    id := ()
    data := ()
    as := #v[pk, sk]
  }
  fromRepr
  | {id, data, as} =>
    let pk := as[0]
    let sk := as[1]
    { pk, sk }
  from_to | {pk, sk} => by rfl
  to_from
  | {id, data, as} => by
    simp_all <;> grind
  sizeOf_eq | {pk, sk} => by simp +arith [ALaCarte.FunctorSizeOf.sizeOf]

public instance: ALaCarte.RepresentableDecidableEq BytesPart.Functor where
public instance: ALaCarte.RepresentableOrd BytesPart.Functor where
public instance: Bytes.Part BytesPart.Functor where

public
def BytesPart.length [Bytes.Def]: Bytes.length.Part BytesPart.Functor :=
  fun _ _ =>
    32

end Dh

#combine into Bytes, Bytes.length from
  DhPk,
  Dh,

variable [Bytes.Def] [Bytes.Has BytesPart.Functor]

public
abbrev DhPk.BytesPart.Functor.pack (x: DhPk.BytesPart.Functor Bytes) := BytesView.pack x

public
abbrev Dh.BytesPart.Functor.pack (x: Dh.BytesPart.Functor Bytes) := BytesView.pack x

public
instance: CanDH Bytes where
  dhPk sk :=
    ({sk}: DhPk.BytesPart.Functor Bytes).pack

  dh pk sk :=
    match pk.view? DhPk.BytesPart.Functor with
    | some { sk := sk2 } =>
      if sk ≤ sk2 then
        ({sk := sk, pk := ({sk := sk2}: DhPk.BytesPart.Functor Bytes).pack}: Dh.BytesPart.Functor Bytes).pack
      else
        ({sk := sk2, pk := ({sk := sk}: DhPk.BytesPart.Functor Bytes).pack}: Dh.BytesPart.Functor Bytes).pack
    | none =>
      ({sk, pk}: Dh.BytesPart.Functor Bytes).pack

public
theorem dh_commutes
  (sk1 sk2: Bytes)
  : dh (dhPk sk1) sk2 = dh (dhPk sk2) sk1
:= by
  simp only [dhPk, dh, BytesView.view_pack]
  grind

grind_pattern dh_commutes => dh (dhPk sk1) sk2, dh (dhPk sk2) sk1

end Constructors

section AttackerKnowledge

public
def dhPk.attackerKnows [Bytes.Def] [Bytes.Has BytesPart.Functor]: Bytes.AttackerKnows.Part BytesPart.Functor where
  pred p out :=
    ∃ sk,
      out = dhPk sk ∧
      p sk

public
def dh.attackerKnows [Bytes.Def] [Bytes.Has BytesPart.Functor]: Bytes.AttackerKnows.Part BytesPart.Functor where
  pred p out :=
    ∃ pk sk,
      out = dh pk sk ∧
      p pk ∧
      p sk

#combine [Bytes.Has BytesPart.Functor] into Bytes.AttackerKnows.merge from
  dhPk,
  dh,

variable [Bytes.Def] [Bytes.Has BytesPart.Functor]
variable [ExecTrace.Def] [Trace.BaseAttackerKnows.Def]
variable [Bytes.AttackerKnows.Def] [Bytes.AttackerKnows.Has attackerKnows]

public
theorem attacker_knows_dhPk
  (sk: Bytes) (tr: ExecTrace)
  : sk.AttackerKnows tr →
    (dhPk sk).AttackerKnows tr
:= by
  intro h_inp
  apply Bytes.AttackerKnows.prove dhPk.attackerKnows
  simp only [dhPk.attackerKnows]
  grind

public
theorem attacker_knows_dh
  (pk sk: Bytes) (tr: ExecTrace)
  : pk.AttackerKnows tr →
    sk.AttackerKnows tr →
    (dh pk sk).AttackerKnows tr
:= by
  intro h_pk h_sk
  apply Bytes.AttackerKnows.prove dh.attackerKnows
  simp only [dh.attackerKnows]
  grind

end AttackerKnowledge

namespace Broken

variable [Bytes.Def]

-- not exposed to the attacker through attacker knowledge,
-- but through a Traceful function
public
def dhPkInvert [Bytes.Has BytesPart.Functor] (pk: Bytes): Err Bytes :=
  match pk.view? DhPk.BytesPart.Functor with
  | some { sk } => some sk
  | none => none

public
theorem dhPkInvert_dhPk
  [Bytes.Has BytesPart.Functor]
  (sk: Bytes)
  : dhPkInvert (dhPk sk) = some sk
:= by
  simp only [dhPk, dhPkInvert]
  grind

public
theorem dhPk_dhPkInvert
  [Bytes.Has BytesPart.Functor]
  (pk: Bytes)
  : match dhPkInvert pk with
    | none => True
    | some sk => dhPk sk = pk
:= by
  simp only [dhPk, dhPkInvert]
  grind

public
structure BrokenDhEvent where
  brokenPk: Bytes

#combine into ExecTrace, Trace.BaseAttackerKnows from ProtocolEvent BrokenDhEvent

variable [ExecTrace.Def] [ExecTrace.Has TracePart.Exec]

public
def ThisDhPkHasBeenBroken (brokenPk: Bytes) (tr: ExecTrace): Prop :=
  tr.EventLogged ({brokenPk}: BrokenDhEvent)

theorem ThisDhPkHasBeenBroken_later
  (brokenPk: Bytes) (tr1 tr2: ExecTrace)
  : tr1 ≤ tr2 →
    ThisDhPkHasBeenBroken brokenPk tr1 →
    ThisDhPkHasBeenBroken brokenPk tr2
:= by
  simp only [ThisDhPkHasBeenBroken]
  grind

grind_pattern ThisDhPkHasBeenBroken_later => tr1 ≤ tr2, ThisDhPkHasBeenBroken brokenPk tr1

public
def OneDhPkHasBeenBroken (tr: ExecTrace): Prop :=
  ∃ brokenPk, ThisDhPkHasBeenBroken brokenPk tr

theorem OneDhPkHasBeenBroken_later
  (tr1 tr2: ExecTrace)
  : tr1 ≤ tr2 →
    OneDhPkHasBeenBroken tr1 →
    OneDhPkHasBeenBroken tr2
:= by
  simp only [OneDhPkHasBeenBroken]
  grind

grind_pattern OneDhPkHasBeenBroken_later => tr1 ≤ tr2, OneDhPkHasBeenBroken tr1

@[expose]
public
def label (brokenPk: Bytes): Label where
  isCorrupt tr := ThisDhPkHasBeenBroken brokenPk tr

variable [Bytes.Has DiffieHellman'.BytesPart.Functor]
variable [ExecTrace.Has Network.TracePart.Exec]

public
def breakDhPk (msgHandle: Nat): Traceful Nat := do
  let pk ← Network.receiveMessage msgHandle
  ProtocolEvent.logEvent ({brokenPk := pk}: BrokenDhEvent)
  let sk ← dhPkInvert pk
  let handle ← Network.sendMessage sk
  return handle

@[expose]
public
def breakDhPk.transitionSystem: TransitionSystem := .make (fun handle => breakDhPk handle)

end Broken

section Invariants

section Definition

variable [ExecTrace.Def] [ProofTrace.Def]
variable [Bytes.Def] [Bytes.Has DiffieHellman'.BytesPart.Functor]
variable [ExecTrace.Has Broken.TracePart.Exec]

public
def DhPk.BytesPart.invariants: Bytes.Invariants.Part DhPk.BytesPart.Functor where
  well_formed := fun {sk := sk} rec tr =>
    (rec sk) tr

  usage := fun {sk := sk} rec tr =>
    Usage.nothing

  label := fun {sk := sk} rec tr =>
    Label.pub

  invariant := fun {sk := sk} rec tr =>
    (sk.label tr).canFlow (Broken.label (dhPk sk)) tr.erase ∧
    (rec sk) tr

public
theorem DhPk.BytesPart.invariantsLawful [Bytes.Invariants.Def]: Bytes.Invariants.Part.Lawful DhPk.BytesPart.invariants where

end Definition

section DhPkLemmas

variable [ExecTrace.Def] [ProofTrace.Def]
variable [Bytes.Def] [Bytes.Has DiffieHellman'.BytesPart.Functor]
variable [ExecTrace.Has Broken.TracePart.Exec]

variable [Bytes.Invariants.Def] [Bytes.Invariants.Has DhPk.BytesPart.invariants]

@[simp]
public
theorem dhPk.WellFormed
  (sk: Bytes) (tr: ProofTrace)
  :
    (dhPk sk).WellFormed tr = sk.WellFormed tr
:= by
  simp [dhPk, Bytes.WellFormed.eq, DhPk.BytesPart.invariants]

@[simp]
public
theorem dhPk.label
  (sk: Bytes) (tr: ProofTrace)
  : (dhPk sk).label tr = Label.pub
:= by
  simp [dhPk, Bytes.label.eq, DhPk.BytesPart.invariants]

@[simp]
public
theorem dhPk.Invariant
  (sk: Bytes) (tr: ProofTrace)
  :
    sk.Invariant tr →
    (sk.label tr).canFlow (Broken.label (dhPk sk)) tr.erase →
    (dhPk sk).Invariant tr
:= by
  simp [dhPk, Bytes.Invariant.eq, DhPk.BytesPart.invariants]
  grind

end DhPkLemmas

section Definition

variable [ExecTrace.Def] [ProofTrace.Def]
variable [Bytes.Def] [Bytes.Has DiffieHellman'.BytesPart.Functor]
variable [ExecTrace.Has Broken.TracePart.Exec]

public
def Dh.BytesPart.invariants: Bytes.Invariants.Part Dh.BytesPart.Functor where
  well_formed := fun {pk, sk} rec tr =>
      (rec pk) tr ∧
      (rec sk) tr

  usage := fun {pk, sk} rec tr =>
    Usage.nothing

  label := fun {pk, sk} rec tr =>
    match _: pk.view? DhPk.BytesPart.Functor with
    | none => Label.pub
    | some {sk := sk2} =>
      Label.join ((rec sk) tr) ((rec sk2) tr)

  invariant := fun {pk, sk} rec tr =>
      (rec pk) tr ∧
      (rec sk) tr

public
theorem Dh.BytesPart.invariantsLawful [Bytes.Invariants.Def] [Bytes.Invariants.Has DhPk.BytesPart.invariants]: Bytes.Invariants.Part.Lawful Dh.BytesPart.invariants where
  label_later := by
    intro _ x rec tr1 tr2
    cases x
    simp_all [DhPk.BytesPart.invariants, BytesPart.invariants, DY.ALaCarte.FunctorSizeOf.sizeOf] <;> grind

end Definition

#combine [Bytes.Has BytesPart.Functor] [ExecTrace.Has Broken.TracePart.Exec] into
  Bytes.Invariants,
  Bytes.Invariants.Lawful [Bytes.Invariants.Has DhPk.BytesPart.invariants]
from
  DhPk,
  Dh,

end Invariants

-- Temporarly close the namespace to define Bytes.dhSkLabel'
end DiffieHellman'

section ExtractDhSk

variable [Bytes.Def]
variable [Bytes.Has DiffieHellman'.BytesPart.Functor]

noncomputable
def DiffieHellman'.extractDhSk (pk: Bytes): Option Bytes :=
  match pk.view? DiffieHellman'.DhPk.BytesPart.Functor with
  | some { sk } =>
    some sk
  | none => none

theorem DiffieHellman'.dhPk_extractDhSk (b: Bytes):
  match extractDhSk b with
  | none => True
  | some sk => b = DiffieHellman'.dhPk sk
:= by
  simp [extractDhSk, DiffieHellman'.dhPk]
  grind

variable [ExecTrace.Def] [ProofTrace.Def]
variable [ExecTrace.Has DiffieHellman'.Broken.TracePart.Exec]

theorem DiffieHellman'.extractDhSk.preserves_WellFormed
  [Bytes.Invariants.Def] [Bytes.Invariants.Has DiffieHellman'.BytesPart.invariants]
: ExtractPreservesWellFormed extractDhSk
:= by
  simp [ExtractPreservesWellFormed]
  grind [DiffieHellman'.dhPk_extractDhSk, DiffieHellman'.dhPk.WellFormed]

public
noncomputable
def Bytes.dhSkLabel'
  [Bytes.Invariants.Def]
  (pk: Bytes) (tr: ProofTrace): Label
:=
  Bytes.xxxLabel DiffieHellman'.extractDhSk pk tr

public
theorem Bytes.dhSkLabel'_dhPk
  [Bytes.Invariants.Def]
  [Bytes.Invariants.Has DiffieHellman'.BytesPart.invariants]
  (sk: Bytes) (tr: ProofTrace)
  : (DiffieHellman'.dhPk sk).dhSkLabel' tr = sk.label tr
:= by
  simp [Bytes.dhSkLabel', Bytes.xxxLabel, DiffieHellman'.extractDhSk, DiffieHellman'.dhPk]
  grind

grind_pattern Bytes.dhSkLabel'_dhPk => (DiffieHellman'.dhPk sk).dhSkLabel' tr

public
theorem Bytes.dhSkLabel'_later
  [Bytes.Invariants.Def]
  [Bytes.Invariants.Has DiffieHellman'.BytesPart.invariants]
  [Bytes.label_later.Proof]
  (b: Bytes) (tr1 tr2: ProofTrace)
  :
    b.WellFormed tr1 →
    tr1 ≤ tr2 →
    b.dhSkLabel' tr1 = b.dhSkLabel' tr2
:= by
  simp [Bytes.dhSkLabel']
  apply Bytes.xxxLabel_later DiffieHellman'.extractDhSk DiffieHellman'.extractDhSk.preserves_WellFormed

grind_pattern Bytes.dhSkLabel'_later => tr1 ≤ tr2, b.dhSkLabel' tr1

public
theorem Bytes.dhSkLabel'_later_fast
  [Bytes.Invariants.Def] [Bytes.Invariants.Lawful]
  [Bytes.Invariants.Has DiffieHellman'.BytesPart.invariants]
  (b: Bytes) (tr1 tr2: ProofTrace)
  :
    b.Invariant tr1 →
    tr1 ≤ tr2 →
    b.dhSkLabel' tr1 = b.dhSkLabel' tr2
:= by grind

grind_pattern [grind_later] Bytes.dhSkLabel'_later_fast => tr1 ≤ tr2, b.dhSkLabel' tr1

end ExtractDhSk

namespace DiffieHellman'
section Invariants

variable [ExecTrace.Def] [ProofTrace.Def]
variable [Bytes.Def] [Bytes.Has BytesPart.Functor]
variable [ExecTrace.Has Broken.TracePart.Exec]
variable [Bytes.Invariants.Def] [Bytes.Invariants.Has BytesPart.invariants]

@[simp]
public
theorem dh.WellFormed
  (pk sk: Bytes) (tr: ProofTrace)
  : (dh pk sk).WellFormed tr = (pk.WellFormed tr ∧ sk.WellFormed tr)
:= by
  simp only [dh]
  split
  · rename_i sk2 heq
    have: pk = dhPk sk2 := by simp_all [dhPk]; grind [dhPk]
    split
    all_goals
      simp [Dh.BytesPart.invariants, DhPk.BytesPart.invariants]
      grind [dhPk.WellFormed]
  · simp [Dh.BytesPart.invariants]

@[simp]
public
theorem dh.label
  (pk sk: Bytes) (tr: ProofTrace)
  : (dh pk sk).label tr = Label.join (pk.dhSkLabel' tr) (sk.label tr)
:= by
  simp only [dh]
  split
  · split
    all_goals
      simp only [Bytes.label.eq, Dh.BytesPart.invariants, Bytes.dhSkLabel', Bytes.xxxLabel, extractDhSk]
      grind
  · simp only [Bytes.label.eq, Dh.BytesPart.invariants, Bytes.dhSkLabel', Bytes.xxxLabel, extractDhSk]
    grind

@[simp]
public
theorem dh.Invariant
  (pk sk: Bytes) (tr: ProofTrace)
  : (
      pk.Invariant tr ∧
      sk.Invariant tr ∧
      (sk.label tr).canFlow (Broken.label (dhPk sk)) tr.erase
    ) → (
      (dh pk sk).Invariant tr
    )
:= by
  simp only [dh]
  split
  · rename_i sk2 heq
    have h_pk: pk = ({ sk := sk2 }: BytesView DhPk.BytesPart.Functor).pack := by grind
    subst h_pk
    split
    · simp [Dh.BytesPart.invariants, DhPk.BytesPart.invariants]
      grind
    · simp [Dh.BytesPart.invariants, DhPk.BytesPart.invariants]
      grind
  · simp [Dh.BytesPart.invariants]
    grind

end Invariants

section HoareTriples

variable [Bytes.Def] [Bytes.Has BytesPart.Functor]
variable [ExecTrace.Def] [ProofTrace.Def]
variable [ExecTrace.Has Broken.TracePart.Exec]
variable [Bytes.Invariants.Def] [Bytes.Invariants.Has BytesPart.invariants]

public
instance
  (sk: Bytes)
  : HoareTriplePure
    (dhPk sk)
    (fun tr =>
      sk.Invariant tr ∧
      (sk.label tr).canFlow (Broken.label (dhPk sk)) tr.erase
    )
    (fun res tr =>
      res.Invariant tr ∧
      res.label tr = Label.pub
      -- and usage
    )
  where
    pf := by
      grind [dhPk.Invariant, dhPk.label]

public
instance
  (pk sk: Bytes)
  : HoareTriplePure
    (dh pk sk)
    (fun tr =>
      sk.Invariant tr ∧
      (sk.label tr).canFlow (Broken.label (dhPk sk)) tr.erase ∧
      pk.Publishable tr
      -- and usage
    )
    (fun res tr =>
      res.Invariant tr ∧
      res.label tr = Label.join (sk.label tr) (pk.dhSkLabel' tr)
      -- and usage
    )
  where
    pf := by
      grind [dh.Invariant, dh.label]

end HoareTriples

section AttackerKnowledgeTheorem

variable [ExecTrace.Def] [ProofTrace.Def] [Trace.Invariant.Def]
variable [Bytes.Def] [Bytes.Invariants.Def]
variable [Bytes.Has BytesPart.Functor]
variable [ExecTrace.Has Broken.TracePart.Exec]
variable [Bytes.Invariants.Has BytesPart.invariants]

public
instance: Bytes.AttackerKnows_implies_Publishable.Part dhPk.attackerKnows where
  pf := by
    simp only [dhPk.attackerKnows]
    intro out tr h_tr ⟨sk, ⟨ h_out, h_sk ⟩⟩
    subst h_out
    simp_all [Bytes.Publishable]
    grind [dhPk.Invariant, canFlowTrans]

public
instance: Bytes.AttackerKnows_implies_Publishable.Part dh.attackerKnows where
  pf := by
    simp only [dh.attackerKnows]
    intro out tr h_tr ⟨pk, sk, ⟨ h_out, h_inputs ⟩⟩
    subst h_out
    simp_all [Bytes.Publishable]
    grind [dh.Invariant, canFlowTrans]

end AttackerKnowledgeTheorem
section AttackerKnowledgeTheorem

#combine [Bytes.Has BytesPart.Functor] [ExecTrace.Has Broken.TracePart.Exec] [Bytes.Invariants.Has BytesPart.invariants] into Bytes.AttackerKnows_implies_Publishable.merge from
  dhPk,
  dh

end AttackerKnowledgeTheorem

namespace Broken

variable [Bytes.Def] [ExecTrace.Def] [ProofTrace.Def] [Trace.Invariant.Def] [Bytes.Invariants.Def]
variable [Bytes.Has DiffieHellman'.BytesPart.Functor]
variable [ExecTrace.Has Broken.TracePart.Exec]
variable [Bytes.Invariants.Has DiffieHellman'.BytesPart.invariants]

@[instance]
theorem dhPkInvert.proof (pk: Bytes)
  : HoareTriple
    (dhPkInvert pk)
    (fun tr => tr.erase.EventLogged ({brokenPk := pk}: Broken.BrokenDhEvent) ∧ pk.Publishable tr)
    (fun sk tr => sk.Publishable tr)
:= by
  apply HoareTriple.mk
  dsimp only [hoareTriple, wp, OptionT.run]
  intro tr h_pk h_tr
  split
  · grind
  rename_i sk _
  have: pk = dhPk sk := by grind [dhPk_dhPkInvert pk]
  have h: (dhPk sk).Publishable tr := by grind
  simp only [dhPk, Bytes.Publishable] at h
  simp only [Bytes.Invariant.eq, DiffieHellman'.DhPk.BytesPart.invariants] at h
  simp only [Label.canFlow, Broken.label, Broken.ThisDhPkHasBeenBroken] at h
  simp only [Bytes.Publishable]
  grind

public
instance: ProtocolEvent.EventInv (BrokenDhEvent) where
  invariant _ _ := True

#combine into
  ProofTrace,
  Trace.Invariant,
  Trace.BaseAttackerKnows_implies_Publishable,
from ProtocolEvent Broken.BrokenDhEvent

variable [Bytes.Invariants.Lawful]
variable [ExecTrace.Has Network.TracePart.Exec]
variable [ProofTrace.Has Broken.TracePart.Proof] [ProofTrace.Has Network.TracePart.Proof]
variable [Trace.Invariant.Has Network.TracePart.Proof]
variable [Trace.Invariant.Has Broken.TracePart.Proof]

@[instance]
theorem breakDhPk.proof (msgHandle: Nat)
  : HoareTriple
    (breakDhPk msgHandle)
    (fun _ => True)
    (fun _ _ => True)
:= by
  unfold breakDhPk
  step
  step by simp [ProtocolEvent.EventInv.invariant]
  step
  step
  grind

public instance: Trace.Reachable_implies_Invariant.Part breakDhPk.transitionSystem := .mk (fun (msgHandle) => breakDhPk.proof msgHandle)

end Broken

end DY.DiffieHellman'
