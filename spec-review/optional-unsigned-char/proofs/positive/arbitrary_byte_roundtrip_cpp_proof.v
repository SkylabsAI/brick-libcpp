
(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.optional.spec.
Require Import skylabs.brick.libstdcpp.test.optional.arbitrary_byte_roundtrip_cpp.

#[local] Set Default Goal Selector "!".

Section with_cpp.
  Context `{Σ : cpp_logic} `{MOD : source ⊧ σ}.

  cpp.spec "arbitrary_byte_roundtrip()" default.
  Lemma test_arbitrary_byte_roundtrip :
    verify[source] "arbitrary_byte_roundtrip()".
  Proof using MOD. verify_spec; go.
    iExists (Vint 1); go.
    - iExists (1$c)%cQp; go.
    - iExists (Vint 254); go.
      + iExists (1$c)%cQp; go.
  Qed.
End with_cpp.
