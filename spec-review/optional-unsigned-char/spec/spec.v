(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.spec.
Require Export skylabs.brick.libstdcpp.optional.hints.
Require Import skylabs.brick.libstdcpp.optional.inc_optional_cpp.

Section with_cpp.
  Context `{Σ : cpp_logic, inc_optional_cpp.source ⊧ σ}.

  cpp.spec "std::optional<unsigned char>::optional(std::nullopt_t)"
    as nullopt_ctor_spec from inc_optional_cpp.source with (fun (this : ptr) =>
      \arg{tag} "#0" (Vptr tag)
      \post this |-> optionalR 1$m empty).

  cpp.spec "std::optional<unsigned char>::optional<unsigned char, 1b>(unsigned char&&)"
    as value_ctor_rvalue_spec from inc_optional_cpp.source with (fun (this : ptr) =>
      \arg{source} "__t" (Vref source)
      \prepost{q byte} source |-> ucharR q byte
      \post this |-> optionalR 1$m (engaged byte)).

  cpp.spec "std::optional<unsigned char>::optional<unsigned char&, 1b>(unsigned char&)"
    as value_ctor_lvalue_spec from inc_optional_cpp.source with (fun (this : ptr) =>
      \arg{source} "__t" (Vref source)
      \prepost{q byte} source |-> ucharR q byte
      \post this |-> optionalR 1$m (engaged byte)).

  cpp.spec "std::optional<unsigned char>::has_value() const"
    as has_value_spec from inc_optional_cpp.source with (fun (this : ptr) =>
      \prepost{q s} this |-> optionalR q s
      \post[Vbool (has_value s)] emp).

  cpp.spec "std::optional<unsigned char>::operator*() const &"
    as deref_const_lvalue_spec from inc_optional_cpp.source with
      (fun (this : ptr) =>
        \prepost{q byte} this |-> optionalR q (engaged byte)
        \post[Vref (optional_value_ptr this)] emp).

  cpp.spec "std::optional<unsigned char>::~optional()"
    as destructor_spec from inc_optional_cpp.source with (fun (this : ptr) =>
      \pre{s} this |-> optionalR 1$m s
      \post emp).

End with_cpp.
