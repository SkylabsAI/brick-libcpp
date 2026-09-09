(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Export skylabs.brick.libstdcpp.optional.model.

sl.lock
Definition empty_byteR `{Σ : cpp_logic, σ : genv} (q : cQp.t) : Rep :=
  structR "std::_Optional_payload_base<unsigned char>::_Empty_byte" q.
#[only(cfracsplittable,type_ptr,lazy_unfold(export))] derive empty_byteR.

sl.lock
Definition storageR `{Σ : cpp_logic, σ : genv}
    (q : cQp.t) (s : state) : Rep :=
  match s with
  | empty =>
      unionR
        "std::_Optional_payload_base<unsigned char>::_Storage<unsigned char, 1b>"
        q (Some 0%nat) **
      _field
        "std::_Optional_payload_base<unsigned char>::_Storage<unsigned char, 1b>::_M_empty"
        |-> empty_byteR q
  | engaged byte =>
      unionR
        "std::_Optional_payload_base<unsigned char>::_Storage<unsigned char, 1b>"
        q (Some 1%nat) **
      _field
        "std::_Optional_payload_base<unsigned char>::_Storage<unsigned char, 1b>::_M_value"
        |-> ucharR q byte
  end.
#[only(cfractional,timeless)] derive storageR.
#[global] Instance storageR_cfrac_valid `{Σ : cpp_logic, σ : genv} :
  CFracValid1 storageR.
Proof. constructor. intros q s. rewrite storageR.unlock. destruct s; apply _. Qed.
#[global] Instance storageR_cfrac_splittable `{Σ : cpp_logic, σ : genv} :
  CFracSplittable_1 storageR := {}.
#[only(lazy_unfold(export))] derive storageR.

sl.lock
Definition payload_baseR `{Σ : cpp_logic, σ : genv}
    (q : cQp.t) (s : state) : Rep :=
  structR "std::_Optional_payload_base<unsigned char>" q **
  _field "std::_Optional_payload_base<unsigned char>::_M_payload"
    |-> storageR q s **
  _field "std::_Optional_payload_base<unsigned char>::_M_engaged"
    |-> boolR q (has_value s).
#[only(cfracsplittable,type_ptr,lazy_unfold(export))] derive payload_baseR.

sl.lock
Definition payloadR `{Σ : cpp_logic, σ : genv}
    (q : cQp.t) (s : state) : Rep :=
  structR "std::_Optional_payload<unsigned char, 1b, 1b, 1b>" q **
  _base "std::_Optional_payload<unsigned char, 1b, 1b, 1b>"
    "std::_Optional_payload_base<unsigned char>" |-> payload_baseR q s.
#[only(cfracsplittable,type_ptr,lazy_unfold(export))] derive payloadR.

sl.lock
Definition optional_base_implR `{Σ : cpp_logic, σ : genv}
    (q : cQp.t) : Rep :=
  structR
    "std::_Optional_base_impl<unsigned char, std::_Optional_base<unsigned char, 1b, 1b>>"
    q.
#[only(cfracsplittable,type_ptr,lazy_unfold(export))] derive optional_base_implR.

sl.lock
Definition optional_baseR `{Σ : cpp_logic, σ : genv}
    (q : cQp.t) (s : state) : Rep :=
  structR "std::_Optional_base<unsigned char, 1b, 1b>" q **
  _base "std::_Optional_base<unsigned char, 1b, 1b>"
    "std::_Optional_base_impl<unsigned char, std::_Optional_base<unsigned char, 1b, 1b>>"
      |-> optional_base_implR q **
  _field "std::_Optional_base<unsigned char, 1b, 1b>::_M_payload"
    |-> payloadR q s.
#[only(cfracsplittable,type_ptr,lazy_unfold(export))] derive optional_baseR.

sl.lock
Definition enable_copy_moveR `{Σ : cpp_logic, σ : genv}
    (q : cQp.t) : Rep :=
  structR
    "std::_Enable_copy_move<1b, 1b, 1b, 1b, std::optional<unsigned char>>"
    q.
#[only(cfracsplittable,type_ptr,lazy_unfold(export))] derive enable_copy_moveR.

sl.lock
Definition optionalR `{Σ : cpp_logic, σ : genv}
    (q : cQp.t) (s : state) : Rep :=
  structR "std::optional<unsigned char>" q **
  _base "std::optional<unsigned char>"
    "std::_Optional_base<unsigned char, 1b, 1b>" |-> optional_baseR q s **
  _base "std::optional<unsigned char>"
    "std::_Enable_copy_move<1b, 1b, 1b, 1b, std::optional<unsigned char>>"
      |-> enable_copy_moveR q.
#[only(cfracsplittable,type_ptr,lazy_unfold(export))] derive optionalR.

(* Use [optional_value_ptr.unlock] when proving facts about the nested byte. *)
sl.lock
Definition optional_value_ptr `{σ : genv} (this : ptr) : ptr :=
  this ,, _base "std::optional<unsigned char>"
      "std::_Optional_base<unsigned char, 1b, 1b>"
    ,, _field "std::_Optional_base<unsigned char, 1b, 1b>::_M_payload"
    ,, _base "std::_Optional_payload<unsigned char, 1b, 1b, 1b>"
      "std::_Optional_payload_base<unsigned char>"
    ,, _field "std::_Optional_payload_base<unsigned char>::_M_payload"
    ,, _field
      "std::_Optional_payload_base<unsigned char>::_Storage<unsigned char, 1b>::_M_value".

#[global] Instance optionalR_learn `{Σ : cpp_logic, σ : genv} :
  AtLearnEqF1 optionalR := ltac:(solve_learnable).

#[global] Instance optionalR_agree `{Σ : cpp_logic, σ : genv}
    q1 q2 s1 s2 :
  Observe2 [| s1 = s2 |] (optionalR q1 s1) (optionalR q2 s2).
Proof.
  apply observe_2_intro_only_provable.
  rewrite !optionalR.unlock !optional_baseR.unlock !payloadR.unlock
    !payload_baseR.unlock !storageR.unlock.
  iIntros "(_ & Hbase1 & _) (_ & Hbase2 & _)".
  iDestruct "Hbase1" as "(_ & _ & Hpayload1)".
  iDestruct "Hbase2" as "(_ & _ & Hpayload2)".
  iDestruct "Hpayload1" as "(_ & Hpayloadbase1)".
  iDestruct "Hpayload2" as "(_ & Hpayloadbase2)".
  iDestruct "Hpayloadbase1" as "(_ & Hstorage1 & Hengaged1)".
  iDestruct "Hpayloadbase2" as "(_ & Hstorage2 & Hengaged2)".
  destruct s1 as [|byte1], s2 as [|byte2].
  - done.
  - iDestruct (observe_2 [| false = true |]
      with "Hengaged1 Hengaged2") as %H. discriminate H.
  - iDestruct (observe_2 [| true = false |]
      with "Hengaged1 Hengaged2") as %H. discriminate H.
  - iDestruct "Hstorage1" as "(_ & Hbyte1)".
    iDestruct "Hstorage2" as "(_ & Hbyte2)".
    iDestruct (observe_2 [| byte1 = byte2 |]
      with "Hbyte1 Hbyte2") as %->. done.
Qed.
