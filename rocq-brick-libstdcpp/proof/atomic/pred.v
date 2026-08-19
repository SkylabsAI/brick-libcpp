(**
 * Copyright (C) 2025 SkyLabs AI, Inc.
 * All rights reserved.
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BlueRock Exception for use over network, see repository root for details.
 *)
Require Import skylabs.auto.cpp.spec.
Require Import skylabs.cpp.spec.concepts.
Require skylabs.brick.libstdcpp.atomic.inc_int_cpp.

Require Import skylabs.cpp.spec.concepts.

(** * Interface to Atomic<T> *)
(**
These specifications assume that all memory order parameters (template,
function arguments) are _SEQ_CST. In the C++ code, redefine the other
memory order macros to __ATOMIC_SEQ_CST.
*)

cpp.enum "std::memory_order" from (inc_int_cpp.source) variant.
#[global] Abbreviation Tmemory_order := {%cpp_type[inc_int_cpp.source] "std::memory_order"} (only parsing).

Module Type ATOMIC_PREDS.

  (** Type [t] indexing our spec models the type name T in Atomic<T>. *)

  (** The type where the actual methods are implemented *)
  #[global] Abbreviation base_name ty :=
    (Ninst "std::__atomic_base" [Atype ty; Avalue (Eint 0 Tbool)]).
  #[global] Abbreviation base_name1 ty :=
    (Ninst "std::__atomic_base" [Atype ty; Avalue (Eint 1 Tbool)]).
  (** The type <<std::atomic<T>>> *)
  #[global] Abbreviation class_name ty := (Ninst "std::atomic" [Atype ty]).
  #[global] Abbreviation T ty := (Tnamed (class_name ty)).

  (** Abstract predicates *)

  (** Fraction [q] ownership of atomically accessible value [v]. *)
  Parameter R : ∀ `{Σ : cpp_logic} {σ : genv} (ty : type) `{PV : @PrimVal ty A} (q : cQp.t) (x : A), Rep.

  Section R_props.
    Context `{Σ : cpp_logic} {σ : genv} `{PV : @PrimVal ty A}.
    Abbreviation R := (R ty (PV:=PV)).

    #[global] Declare Instance R_frac : CFractional1 R.
    #[global] Declare Instance R_timeless : Timeless2 R.
    #[global] Declare Instance R_frac_valid : CFracValid1 R.
    #[global] Declare Instance R_agree : Cbn (Learn (any ==> learn_eq ==> learn_hints.fin) R).
    #[global] Declare Instance R_type : Typed2 (class_name ty) R.
  End R_props.

End ATOMIC_PREDS.

Declare Module atomic : ATOMIC_PREDS.
