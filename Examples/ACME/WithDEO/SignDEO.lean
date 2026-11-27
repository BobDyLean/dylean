module

public import DY.EquationalTheory.Sign

namespace DY.Example.ACME.WithDEO.SignDEO

section Constructors

namespace DEO

public
structure BytesPart.Functor (Bytes: Type) where
  msg: Bytes
  sig: Bytes

public
instance: ALaCarte.FunctorSizeOf BytesPart.Functor where
  sizeOf | {msg, sig} => sizeOf msg + sizeOf sig

public
instance: ALaCarte.Representable BytesPart.Functor where
  CtorId := Unit
  ctors | () => { Data := Unit, nRec := 2 }

  toRepr | {msg, sig} => {
    id := ()
    data := ()
    as := #v[msg, sig]
  }
  fromRepr
  | {id, data, as} =>
    let msg := as[0]
    let sig := as[1]
    { msg, sig }
  from_to | {msg, sig} => by rfl
  to_from
  | {id, data, as} => by
    simp_all <;> grind
  sizeOf_eq | {msg, sig} => by simp +arith [ALaCarte.FunctorSizeOf.sizeOf]

public instance: ALaCarte.RepresentableDecidableEq BytesPart.Functor where
public instance: ALaCarte.RepresentableOrd BytesPart.Functor where
public instance: Bytes.Part BytesPart.Functor where

public
def BytesPart.length [Bytes.Def]: Bytes.length.Part BytesPart.Functor :=
  fun _ _ =>
    32

end DEO

#combine into Bytes, Bytes.length from
  Signature.Vk,
  Signature.Sign,
  DEO
variable [Bytes.Def] [Bytes.Has BytesPart.Functor]

public abbrev __root__.DY.Signature.Vk.BytesPart.Functor.pack (x: Signature.Vk.BytesPart.Functor Bytes) := BytesView.pack x
public abbrev __root__.DY.Signature.Vk.BytesPart.Functor.Sign.BytesPart.Functor.pack (x: Signature.Sign.BytesPart.Functor Bytes) := BytesView.pack x
public abbrev DEO.BytesPart.Functor.pack (x: DEO.BytesPart.Functor Bytes) := BytesView.pack x

public
instance: Signature.CanSign Bytes where
  vk sk :=
    ({sk}: Signature.Vk.BytesPart.Functor Bytes).pack

  sign sk nonce msg :=
    ({sk, nonce, msg}: Signature.Sign.BytesPart.Functor Bytes).pack

  verify vk msg sig :=
    match sig.view? Signature.Sign.BytesPart.Functor, vk.view? Signature.Vk.BytesPart.Functor with
    | some { sk := skSig, nonce := _, msg := msgSig }, some { sk := skVk } =>
      (
        skSig = skVk && msg = msgSig
      ) || (
        match skVk.view? DEO.BytesPart.Functor with
        | some { msg := msgDeo, sig := sigDeo } =>
          sig = sigDeo && msg = msgDeo
        | none => false
      )
    | _, _ => false

public
def deogen (msg sig: Bytes): Bytes :=
  ({msg, sig}: DEO.BytesPart.Functor Bytes).pack

public
theorem verify_sign
  (sk nonce msg: Bytes)
  : Signature.verify (Signature.vk sk) msg (Signature.sign sk nonce msg) = true
:= by
  simp only [Signature.verify, Signature.vk, Signature.sign]
  grind

public
theorem verify_deo
  (sk nonce msg1 msg2: Bytes)
  : Signature.verify (Signature.vk (deogen msg2 (Signature.sign sk nonce msg1))) msg2 (Signature.sign sk nonce msg1) = true
:= by
  simp only [Signature.verify, Signature.vk, Signature.sign, deogen]
  grind

end Constructors

section AttackerKnowledge

public
def vk.attackerKnows [Bytes.Def] [Bytes.Has BytesPart.Functor]: Bytes.AttackerKnows.Part BytesPart.Functor where
  pred p out :=
    ∃ sk,
      out = Signature.vk sk ∧
      p sk

public
def sign.attackerKnows [Bytes.Def] [Bytes.Has BytesPart.Functor]: Bytes.AttackerKnows.Part BytesPart.Functor where
  pred p out :=
    ∃ sk nonce msg,
      out = Signature.sign sk nonce msg ∧
      p sk ∧
      p nonce ∧
      p msg

public
def deogen.attackerKnows [Bytes.Def] [Bytes.Has BytesPart.Functor]: Bytes.AttackerKnows.Part BytesPart.Functor where
  pred p out :=
    ∃ msg sig,
      out = deogen msg sig ∧
      p msg ∧
      p sig

#combine [Bytes.Has BytesPart.Functor] into Bytes.AttackerKnows.merge from
  vk,
  sign,
  deogen

variable [Bytes.Def] [Bytes.Has BytesPart.Functor]
variable [ExecTrace.Def] [Trace.BaseAttackerKnows.Def]
variable [Bytes.AttackerKnows.Def] [Bytes.AttackerKnows.Has attackerKnows]

public
theorem attacker_knows_vk
  (sk: Bytes) (tr: ExecTrace)
  : sk.AttackerKnows tr →
    (Signature.vk sk).AttackerKnows tr
:= by
  intro h_inp
  apply Bytes.AttackerKnows.prove vk.attackerKnows
  simp only [vk.attackerKnows]
  grind

public
theorem attacker_knows_sign
  (sk nonce msg: Bytes) (tr: ExecTrace)
  : sk.AttackerKnows tr →
    nonce.AttackerKnows tr →
    msg.AttackerKnows tr →
    (Signature.sign sk nonce msg).AttackerKnows tr
:= by
  intro h_inp h_nonce h_msg
  apply Bytes.AttackerKnows.prove sign.attackerKnows
  simp only [sign.attackerKnows]
  grind

public
theorem attacker_knows_deogen
  (msg sig: Bytes) (tr: ExecTrace)
  : msg.AttackerKnows tr →
    sig.AttackerKnows tr →
    (deogen msg sig).AttackerKnows tr
:= by
  intro h_msg h_sig
  apply Bytes.AttackerKnows.prove deogen.attackerKnows
  simp only [deogen.attackerKnows]
  grind

end AttackerKnowledge

end DY.Example.ACME.WithDEO.SignDEO
