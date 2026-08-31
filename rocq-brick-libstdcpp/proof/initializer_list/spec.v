(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.spec.
Require Export skylabs.cpp.slice.

Require Import skylabs.cpp.spec.concepts.

Require Import skylabs.brick.libstdcpp.initializer_list.inc_initializer_list_cpp.
Require Import skylabs.brick.libstdcpp.initializer_list.inc_initializer_list_cpp_templates.

NES.Begin std.
  #[local] Open Scope Z_scope.

  NES.Begin initializer_list.
    (**
        Module [std.initializer_list] provides specifications for
        <<std::initializer_list<ty> >>.

        # The spine

        A <<std::initializer_list>> refers to a backing array
        (<https://eel.is/c++draft/dcl.init.list#5>) that the *language*, not the
        library, creates: [Einitlist_std] in BRiCk builds one by calling the
        constructor specified below.

        [spineR] owns the object itself. Its model [M] is the pair the three
        accessors pin down -- <<begin()>>, <<end()>> and <<size()>>, with
        <<end() - begin() == size()>>.

        # The payload

        Like [std.vector], the spine owns only the shape. The elements live at
        [arrayp] and are owned separately, via [array_sliceR]:
        <<
          p |-> std.initializer_list.spineR ty q (Mk arrayp (lengthN xs)) **
          arrayp |-> array_sliceR ty 0 (lengthZ xs) Rpayload xs
        >>
        [R_at] and [R] below bundle the two for convenience. Keeping them
        separable matters more here than for other containers, because a
        <<std::initializer_list>> is a *view*: the backing array is a temporary
        whose storage has automatic duration tied to the enclosing
        full-expression, not to the <<initializer_list>> object. Bundling
        unconditionally would suggest the object owns storage it does not control.

        LIMITATION: these specifications are *axiomatized*, not proved against
          libstdc++'s implementation, even though [spineR] is stated in terms of
          its fields.

        LIMITATION: BRiCk does not support the lifetime-extended form
          <<std::initializer_list<int> il = {1,2,3};>>, which needs scope-extruded
          temporaries. Uses where the backing array dies with the enclosing
          full-expression -- passing a braced-init-list to a function, or to a
          constructor taking an <<initializer_list>> -- are supported.
     *)

    (** The backing array and its length: the information content
        <<begin()>>/<<end()>>/<<size()>> pin down.

        NOTE declared before the [N] abbreviation below, which would otherwise
        shadow the [N] of [len]. *)
    Record M : Type := Mk { arrayp : ptr ; len : N }.

    #[global] Abbreviation N ty := (Ninst "std::initializer_list" [Atype ty]) (only parsing).
    #[global] Abbreviation T ty := (Tnamed (N ty)) (only parsing).

    (** Ownership of the <<std::initializer_list>> object alone.

        NOTE the field names are libstdc++'s; this package specifies that
        implementation. Nothing outside this definition depends on them. *)
    sl.lock
    Definition spineR `{Σ : cpp_logic, σ : genv} (ty : type) (q : cQp.t) (m : M) : Rep :=
      structR (N ty) q **
      _field (N ty .:: Nid "_M_array") |-> ptrR<Tconst ty> q m.(arrayp) **
      _field (N ty .:: Nid "_M_len") |-> primR Tsize_t q (Vn m.(len)).
    #[only(cfracsplittable,type_ptr,lazy_unfold(global))] derive spineR.

    (** Spine and payload together, for a known backing array.

        NOTE the spine and the payload carry *separate* fractions. They are
        genuinely different resources: the <<initializer_list>> object may well
        be mutable (a freshly materialized temporary is), while the backing
        array is an array of <<const E>>
        (<https://eel.is/c++draft/dcl.init.list#5>) and so is owned constly. *)
    #[global] Abbreviation R_at ty q qx p xs :=
      ( spineR ty q (Mk p (lengthN xs)) **
        pureR (p |-> array_sliceR ty 0 (lengthZ xs) (objR ty qx) xs) )%I
      (q in scope cQp_scope, qx in scope cQp_scope).

    (** Spine and payload together, hiding the backing array. *)
    #[global] Abbreviation R ty q qx xs := (∃ p, R_at ty q qx p xs)%I
      (q in scope cQp_scope, qx in scope cQp_scope).

    Section with_cpp.
      Context `{Σ : cpp_logic, σ : genv}.
      Context (ty : type).

      #[local] Abbreviation spineR := (spineR ty).

      #[global] Instance: LearnEqF1 spineR := ltac:(solve_learnable).

      (** <<constexpr initializer_list(const E*, size_t) noexcept;>>

          The constructor the *compiler* calls for a braced-init-list; it is
          private, and [wp_init_initlist_std] in BRiCk reduces [Einitlist_std] to
          a call of it. See [std_initlist_ctor] there. *)
      cpp.spec "std::initializer_list<$ty>::initializer_list(const $ty*, unsigned long)"
        as ctor from source templates templates (
        \\with
        \this this
        \arg{p} "" (Vptr p)
        \arg{n} "" (Vn n)
        \post this |-> spineR (cQp.m 1) (Mk p n)
      ).

      (** <<constexpr initializer_list() noexcept;>>

          <https://eel.is/c++draft/support.initlist.cons> -- an empty list. The
          backing array is empty, so there is no payload. *)
      cpp.spec "std::initializer_list<$ty>::initializer_list()"
        as default_ctor from source templates templates (
        \\with
        \this this
        \post Exists p, this |-> spineR (cQp.m 1) (Mk p 0)
      ).

      (** The (trivial) destructor.

          NOTE this is needed even though <<std::initializer_list>> owns
          nothing: a braced-init-list passed to a function creates a temporary
          <<initializer_list>>, and the enclosing full-expression destroys it.
          It consumes only the spine -- the backing array is a separate
          temporary with its own lifetime. *)
      cpp.spec "std::initializer_list<$ty>::~initializer_list()"
        as dtor from source templates templates (
        \\with
        \this this
        \pre{m} this |-> spineR (cQp.m 1) m
        \post emp
      ).

      (** <<constexpr size_t size() const noexcept;>>

          <https://eel.is/c++draft/support.initlist.access> *)
      cpp.spec "std::initializer_list<$ty>::size() const"
        as size from source templates templates (
        \\with
        \this this
        \prepost{q m} this |-> spineR q m
        \post[Vn m.(len)] emp
      ).

      (** <<constexpr const E* begin() const noexcept;>>

          <https://eel.is/c++draft/support.initlist.access> *)
      cpp.spec "std::initializer_list<$ty>::begin() const"
        as begin from source templates templates (
        \\with
        \this this
        \prepost{q m} this |-> spineR q m
        \post[Vptr m.(arrayp)] emp
      ).

      (** <<constexpr const E* end() const noexcept;>>

          <https://eel.is/c++draft/support.initlist.access>: one past the last
          element, i.e. [begin() + size()]. *)
      cpp.spec "std::initializer_list<$ty>::end() const"
        as end_ from source templates templates (
        \\with
        \this this
        \prepost{q m} this |-> spineR q m
        \post[Vptr (m.(arrayp) .[ ty ! Z.of_N m.(len) ])] emp
      ).

      (** NOTE templated [cpp.spec]s are indexed by the translation unit they
          were resolved against, so this bundle is too: clients write
          <<std.initializer_list.specs ty source>>. *)
      Definition specs (tu : translation_unit) :=
        ctor tu ** default_ctor tu ** dtor tu ** size tu ** begin tu ** end_ tu.
      #[global] Hint Opaque specs : typeclass_instances sl_opacity.
      #[only(knowledge)] derive specs.
    End with_cpp.
  NES.End initializer_list.
NES.End std.
