(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.spec.

Inductive state : Type :=
| empty
| engaged (byte : Z).

Definition has_value (s : state) : bool :=
  match s with
  | empty => false
  | engaged _ => true
  end.

Succeed Example empty_has_no_value : has_value empty = false := eq_refl.
Succeed Example engaged_zero_has_value : has_value (engaged 0) = true := eq_refl.
Succeed Example engaged_one_has_value : has_value (engaged 1) = true := eq_refl.
Succeed Example engaged_five_has_value : has_value (engaged 5) = true := eq_refl.
Succeed Example engaged_255_has_value : has_value (engaged 255) = true := eq_refl.
