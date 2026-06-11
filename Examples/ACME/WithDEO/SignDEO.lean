module

public import DY.EquationalTheory.Sign

namespace DY.Example.ACME.WithDEO.SignDEO

section Constructors

namespace DEO

public
structure SubF (Bytes: Type) where
  msg: Bytes
  sig: Bytes

public
instance: ALaCarte.FunctorSizeOf SubF where
  sizeOf | {msg, sig} => sizeOf msg + sizeOf sig

public
instance: ALaCarte.Representable SubF where
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

public instance: ALaCarte.RepresentableDecidableEq SubF where
public instance: ALaCarte.RepresentableOrd SubF where
public instance: SubBytesFunctor SubF where

public
def SubF.length [BytesFunctor]: Bytes.PartialLength SubF :=
  fun _ _ =>
    32

end DEO

#combine into BytesFunctor, BytesLength from
  Signature.Vk,
  Signature.Sign,
  DEO
variable [BytesFunctor] [BytesFunctor.Has SubF]

public abbrev __root__.DY.Signature.Vk.SubF.pack (x: Signature.Vk.SubF Bytes) := BytesView.pack x
public abbrev __root__.DY.Signature.Vk.SubF.Sign.SubF.pack (x: Signature.Sign.SubF Bytes) := BytesView.pack x
public abbrev DEO.SubF.pack (x: DEO.SubF Bytes) := BytesView.pack x

public
instance: Signature.CanSign Bytes where
  vk sk :=
    ({sk}: Signature.Vk.SubF Bytes).pack

  sign sk nonce msg :=
    ({sk, nonce, msg}: Signature.Sign.SubF Bytes).pack

  verify vk msg sig :=
    match sig.view? Signature.Sign.SubF, vk.view? Signature.Vk.SubF with
    | some { sk := skSig, nonce := _, msg := msgSig }, some { sk := skVk } =>
      (
        skSig = skVk && msg = msgSig
      ) || (
        match skVk.view? DEO.SubF with
        | some { msg := msgDeo, sig := sigDeo } =>
          sig = sigDeo && msg = msgDeo
        | none => false
      )
    | _, _ => false

public
def deogen (msg sig: Bytes): Bytes :=
  ({msg, sig}: DEO.SubF Bytes).pack

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
def vk.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF]: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ sk,
      out = Signature.vk sk ∧
      p sk

public
def sign.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF]: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ sk nonce msg,
      out = Signature.sign sk nonce msg ∧
      Kleene.Forall p [sk, nonce, msg]

public
def deogen.attackerKnowledge [BytesFunctor] [BytesFunctor.Has SubF]: SubAttackerKnowledge SubF where
  pred p out :=
    ∃ msg sig,
      out = deogen msg sig ∧
      Kleene.Forall p [msg, sig]

#combine [BytesFunctor.Has SubF] into attackerKnowledge' from
  vk,
  sign,
  deogen

variable [BytesFunctor] [BytesFunctor.Has SubF]
variable [ExecTraceTypes] [BaseAttackerKnowledge]
variable [AttackerKnowledge] [AttackerKnowledge.Has attackerKnowledge]

public
theorem attacker_knows_vk
  (sk: Bytes) (tr: ExecTrace)
  : sk.AttackerKnows tr →
    (Signature.vk sk).AttackerKnows tr
:= by
  intro h_inp
  apply Bytes.AttackerKnows.prove vk.attackerKnowledge
  simp only [vk.attackerKnowledge]
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
  apply Bytes.AttackerKnows.prove sign.attackerKnowledge
  simp only [sign.attackerKnowledge, Kleene.Forall]
  grind

public
theorem attacker_knows_deogen
  (msg sig: Bytes) (tr: ExecTrace)
  : msg.AttackerKnows tr →
    sig.AttackerKnows tr →
    (deogen msg sig).AttackerKnows tr
:= by
  intro h_msg h_sig
  apply Bytes.AttackerKnows.prove deogen.attackerKnowledge
  simp only [deogen.attackerKnowledge, Kleene.Forall]
  grind

end AttackerKnowledge

end DY.Example.ACME.WithDEO.SignDEO
