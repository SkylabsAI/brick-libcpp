(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.brick.libstdcpp.initializer_list.spec.
Require Import skylabs.brick.libstdcpp.test.initializer_list.test_cpp.

Require Import skylabs.auto.cpp.prelude.test.

(**
    A client of the <<std::initializer_list>> specifications in
    ../../proof/initializer_list/spec.v.

    [il_size] and [il_first] consume an <<std::initializer_list>> and are
    verified against those (axiomatized) specifications -- [il_size] against the
    spine alone, [il_first] against the bundled (templated) [R_at].

    [use_size] and [use_first] *construct* one from a braced-init-list, so
    verifying them additionally exercises clang's [CXXStdInitializerListExpr]
    and BRiCk's [wp_init_initlist_std].

    [use_ctor] constructs one in the other position a braced-init-list can occupy
    -- the argument of a *constructor* taking an <<initializer_list>>, i.e.
    <<Boxed b{1, 2, 3};>> -- so that building such an object is covered too.
 *)

(** <<Boxed>> has a single field and no user-declared destructor, so its
    representation is just that field. *)
sl.lock
Definition BoxedR `{Σ : cpp_logic, σ : genv} (q : cQp.t) (n : N) : Rep :=
  structR "Boxed" q **
  _field "Boxed::n" |-> primR Tsize_t q (Vn n).
#[only(cfracsplittable,type_ptr,lazy_unfold(global))] derive BoxedR.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.

  #[local] Abbreviation spineR q arrayp n :=
    (std.initializer_list.spineR Tint q arrayp n) (only parsing).
  #[local] Abbreviation R_at q qx arrayp xs :=
    (std.initializer_list.R_at Tint q qx arrayp xs) (only parsing).

  Section specs.
    Context `{MOD : test_cpp.source ⊧ σ}.

    (** Only the spine is needed to read the size. *)
    cpp.spec "il_size(std::initializer_list<int>)" as il_size_spec with
      (\arg{lp} "l" (Vptr lp)
       \prepost{q arrayp n} lp |-> spineR q arrayp n
       \post[Vn n] emp).

    (** Reading an element needs the payload as well, so this is stated against
        the bundled (templated) form [std.initializer_list.R_at]. *)
    cpp.spec "il_first(std::initializer_list<int>)" as il_first_spec with
      (\arg{lp} "l" (Vptr lp)
       \prepost{q qx arrayp x xs} lp |-> R_at q qx arrayp (x :: xs)
       \post[Vint x] emp).

    cpp.spec "use_size()" as use_size_spec with
      (\post[Vn 3] emp).

    cpp.spec "use_first()" as use_first_spec with
      (\post[Vint 7] emp).

    (** The constructor consumes the spine of its argument and records the
        length. It needs only the spine, like [il_size]. *)
    cpp.spec "Boxed::Boxed(std::initializer_list<int>)" as boxed_ctor_spec with
      (\this this
       \arg{lp} "l" (Vptr lp)
       \prepost{q arrayp n} lp |-> spineR q arrayp n
       \post this |-> BoxedR 1$m n).

    (** <<Boxed>> is trivially destructible, but <<b>> still goes out of scope in
        [use_ctor], so the implicit destructor needs a specification. *)
    cpp.spec "Boxed::~Boxed()" as boxed_dtor_spec with
      (\this this
       \pre{n} this |-> BoxedR 1$m n
       \post emp).

    cpp.spec "use_ctor()" as use_ctor_spec with
      (\post[Vn 3] emp).
  End specs.

  Section proofs.
    Context `{MOD : test_cpp.source ⊧ σ}.

    (** [normalize_ptr] reduces <<p .[ ty ! 0 ]>> to [p], which is needed after
        splitting element 0 off an [array_sliceR]; [only_provable_norm] tidies
        the arithmetic side conditions the split leaves behind. *)
    Import normalize.normalize_ptr normalize.only_provable_norm.

    (** [initializer_listR] is abstract, so nothing in a goal determines the
        backing array or its length syntactically. [initializer_listR_learn],
        registered in auto, recovers both; without it every proof below would
        have to instantiate them by hand.

        Only [use_first_ok] below also needs the *fraction* picked for it; it
        opts into [UNSAFE_initializer_listR_learn_q] per invocation with
        <<go using>> rather than registering it for the whole section. The two
        compose: the unsafe hint supplies the fraction while the safe one still
        supplies the backing array and length. *)

    Lemma il_size_ok : verify[ source ] il_size_spec.
    Proof using MOD. verify_spec. go. Qed.
    Definition il_size_B := [LINK] il_size_ok.
    #[local] Hint Resolve il_size_B : sl_opacity.

    (** [array_sliceR_cons] is deliberately not a registered hint -- automation
        cannot guess where to split a slice -- so element 0 is split off by
        hand. [array_sliceR_singleton] *is* registered, so [go] finishes. *)
    Lemma il_first_ok : verify[ source ] il_first_spec.
    Proof using MOD.
      verify_spec. go. rewrite array_sliceR_cons offset_ptr_sub_0 //. go.
      (* give the payload back: the same split, run backwards *)
      rewrite array_sliceR_cons offset_ptr_sub_0 //. go.
    Qed.
    Definition il_first_B := [LINK] il_first_ok.
    #[local] Hint Resolve il_first_B : sl_opacity.

    Lemma use_size_ok : verify[ source ] use_size_spec.
    Proof using MOD.
      verify_spec. go.
    Qed.
    Definition use_size_B := [LINK] use_size_ok.
    #[local] Hint Resolve use_size_B : sl_opacity.

    (** Construct a list *and* read an element of it: the spine is a freshly
        materialized (mutable) temporary while the backing array is <<const>>,
        which is why [R_at] carries the two fractions separately. *)
    Lemma use_first_ok : verify[ source ] use_first_spec.
    Proof using MOD.
      (* the qualified name is deliberate: the hint lives in auto's [hints.wp]
         alongside the rest of the <<std::initializer_list>> automation, and is
         not [Import]ed here. *)
      verify_spec.
      go using skylabs.auto.cpp.hints.wp.UNSAFE_initializer_listR_learn_q.
      (* What is left belongs to [array_sliceR], not [initializer_listR]: the
         payload's fraction and the element split. [pick_frac] does not discharge
         it (the bound [lengthZ xs + 1] needs [xs] first), and no cons-splitting
         hint is registered, so these are supplied by hand. *)
      iExists (cQp.c 1), 7, [8; 9]. go.
    Qed.
    Definition use_first_B := [LINK] use_first_ok.
    #[local] Hint Resolve use_first_B : sl_opacity.

    (** The constructor body is just <<n(l.size())>>, so this is [il_size_ok]
        with the result stored into a field. *)
    Lemma boxed_ctor_ok : verify[ source ] boxed_ctor_spec.
    Proof using MOD. verify_spec. rewrite /BoxedR; go. Qed.
    Definition boxed_ctor_B := [LINK] boxed_ctor_ok.
    #[local] Hint Resolve boxed_ctor_B : sl_opacity.

    Lemma boxed_dtor_ok : verify[ source ] boxed_dtor_spec.
    Proof using MOD. verify_spec. rewrite /BoxedR; go. Qed.
    Definition boxed_dtor_B := [LINK] boxed_dtor_ok.
    #[local] Hint Resolve boxed_dtor_B : sl_opacity.

    (** <<Boxed b{1, 2, 3};>>: the braced-init-list becomes the backing array of
        an <<initializer_list>> temporary, which is then the constructor's
        argument. *)
    Lemma use_ctor_ok : verify[ source ] use_ctor_spec.
    Proof using MOD.
      verify_spec. go.
    Qed.
    Definition use_ctor_B := [LINK] use_ctor_ok.
    #[local] Hint Resolve use_ctor_B : sl_opacity.

    (** TODO a [specs_ok] gluing lemma, of the form
        <<
          denoteModule source ** |> std.initializer_list.specs Tint
          |-- il_size_spec ** il_first_spec ** use_size_spec ** use_first_spec
        >>
        in the style of [std.vector]'s. [work] does not discharge it as written:
        it consumes [std.initializer_list.dtor] once, but all four client
        functions need it, and neither destructing the bundle nor boxing it with
        [|_|] made it reusable. Each client function above *is* separately
        verified against the registered specifications, so this is a packaging
        convenience rather than missing coverage. *)
  End proofs.
End with_cpp.
