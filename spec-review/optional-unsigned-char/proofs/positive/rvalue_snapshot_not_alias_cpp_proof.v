
(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.optional.spec.
Require Import skylabs.brick.libstdcpp.test.optional.rvalue_snapshot_not_alias_cpp.

#[local] Set Default Goal Selector "!".

Section with_cpp.
  Context `{Σ : cpp_logic} `{MOD : source ⊧ σ}.

  cpp.spec "std::move<unsigned char&>(unsigned char&)" from source inline.

  cpp.spec "rvalue_snapshot_not_alias()" default.
  Lemma test_rvalue_snapshot_not_alias :
    verify[source] "rvalue_snapshot_not_alias()".
  Proof using MOD. verify_spec; go.
    iExists (Vint 5); go.
    iExists (1$c)%cQp; go.
  Qed.
End with_cpp.
