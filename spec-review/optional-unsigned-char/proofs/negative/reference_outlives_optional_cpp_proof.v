
(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.optional.spec.
Require Import skylabs.brick.libstdcpp.test.optional.reference_outlives_optional_cpp.

#[local] Set Default Goal Selector "!".

Section with_cpp.
  Context `{Σ : cpp_logic} `{MOD : source ⊧ σ}.

  cpp.spec "reference_outlives_optional()" default.
  Lemma test_reference_outlives_optional :
    verify[source] "reference_outlives_optional()".
  Proof using MOD.

    verify_spec; go.
    try (wpose (optionalR_value_view value_addr (1$m)%cQp 5); go).

  Fail Qed.
  Abort.
End with_cpp.
