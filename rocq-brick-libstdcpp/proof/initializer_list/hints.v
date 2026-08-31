(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.proof.
Require Export skylabs.brick.libstdcpp.initializer_list.spec.

Import linearity.

(**
    Automation for <<std::initializer_list>> construction.

    [wp_init_initlist_std] in BRiCk reduces [Einitlist_std] to a call of the
    constructor named by [std_initlist_ctor]; this hint applies that reduction so
    that [go] can then use the constructor's specification. It lives here rather
    than in <<auto>> because the constructor it lands on is the one *this*
    package specifies -- which is also what lets the availability side condition
    discharge by reduction: libstdc++ declares that constructor.
 *)
Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  Section with_resolve.
    Variables (tu : translation_unit) (ρ : region).

    #[local] Abbreviation wp_init := (wp_init tu ρ).

    Lemma wp_init_initlist_std_hint ty cls aety n (base : ptr) backing Q :
      ((decompose_type ty).2, drop_qualifiers (drop_reference (type_of backing)))
        =[Vm]=> (Tnamed cls, Tarray aety n) ->
      std_initlist_ctor_available tu cls aety =[Vm]=> true ->
      wp_init ty base
        (Econstructor (std_initlist_ctor cls aety)
           [Ecast Carray2ptr backing; Eint (Z.of_N n) Tsize_t] ty) Q
      |-- wp_init ty base (Einitlist_std backing ty) Q.
    Proof.
      rewrite !RedEq_eq_iff => Heq Havail.
      case: Heq => Hcls Harr.
      rewrite -(wp_init_initlist_std tu ρ cls base (decompose_type ty).1 ty backing aety n Q).
      - done.
      - by rewrite {1}(surjective_pairing (decompose_type ty)) Hcls.
      - exact: Harr.
      - exact: Havail.
    Qed.
    Definition wp_init_initlist_std_hint_B := [BWD] wp_init_initlist_std_hint.
  End with_resolve.
End with_cpp.

#[export] Hint Resolve wp_init_initlist_std_hint_B | 150 : db_skylabs_wp.
