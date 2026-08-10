(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.spec.
Require Export skylabs.cpp.slice.

Require Import skylabs.cpp.spec.concepts.

Require Import skylabs.brick.libstdcpp.initializer_list.inc_initializer_list_cpp.

NES.Begin std.
  #[local] Open Scope Z_scope.

  NES.Begin initializer_list.
    #[global] Abbreviation N ty := (Ninst "std::initializer_list" [Atype ty]) (only parsing).
    #[global] Abbreviation T ty := (Tnamed (N ty)) (only parsing).

    (**
        Module [std.initializer_list] provides specifications for
        <<std::initializer_list<ty> >>.

        # The spine

        Unlike the other containers here, the "spine" predicate is *not* defined
        in this file: it is [initializer_listR], provided by BRiCk itself (see
        <<lang/cpp/logic/expr.v>>). That is because the *language*, not the
        library, creates these objects -- <https://eel.is/c++draft/dcl.init.list#5>
        -- so the rule that builds one ([wp_init_initlist_std]) has to be able to
        talk about the result.

        [initializer_listR ty q arrayp n] owns a <<std::initializer_list<ty> >>
        referring to a backing array of [n] elements at [arrayp]. It is abstract:
        <https://eel.is/c++draft/initializer.list.syn> specifies only <<begin()>>,
        <<end()>> and <<size()>> and declares no data members, and since
        <<end() - begin() == size()>>, every conforming representation is
        isomorphic to the pair ([arrayp], [n]). So nothing is lost by declining to
        name fields, and neither BRiCk nor these specifications commit to a
        particular standard library.

        # The payload

        Like [std.vector], the spine owns only the shape. The elements live at
        [arrayp] and are owned separately, via [array_sliceR]:
        <<
          p |-> std.initializer_list.spineR ty q arrayp (lengthN xs) **
          arrayp |-> array_sliceR ty 0 (lengthZ xs) Rpayload xs
        >>
        [R_at] and [R] below bundle the two for convenience. Keeping them
        separable matters more here than for other containers, because a
        <<std::initializer_list>> is a *view*: the backing array is a temporary
        whose storage has automatic duration tied to the enclosing
        full-expression, not to the <<initializer_list>> object. Bundling
        unconditionally would suggest the object owns storage it does not control.

        LIMITATION: these specifications are *axiomatized*, not proved against
          libstdc++'s implementation.

        LIMITATION: BRiCk does not support the lifetime-extended form
          <<std::initializer_list<int> il = {1,2,3};>>, which needs scope-extruded
          temporaries. Uses where the backing array dies with the enclosing
          full-expression -- passing a braced-init-list to a function, or to a
          constructor taking an <<initializer_list>> -- are supported.
     *)

    (** Ownership of the <<std::initializer_list>> object alone.

        NOTE this is [initializer_listR] from BRiCk; the alias exists so that
        client code reads uniformly with [std.vector.spineR] and friends. *)
    #[global] Abbreviation spineR ty q arrayp n := (initializer_listR ty q arrayp n)
      (only parsing).

    (** Spine and payload together, for a known backing array.

        NOTE the spine and the payload carry *separate* fractions. They are
        genuinely different resources: the <<initializer_list>> object may well
        be mutable (a freshly materialized temporary is), while the backing
        array is an array of <<const E>>
        (<https://eel.is/c++draft/dcl.init.list#5>) and so is owned constly. A
        single fraction, as [std.vector.R_alloc_cap] uses, cannot describe that. *)
    #[global] Abbreviation R_at ty q qx arrayp xs :=
      ( spineR ty q arrayp (lengthN xs) **
        pureR (arrayp |-> array_sliceR ty 0 (lengthZ xs) (objR ty qx) xs) )%I
      (q in scope cQp_scope, qx in scope cQp_scope).

    (** Spine and payload together, hiding the backing array. *)
    #[global] Abbreviation R ty q qx xs := (∃ arrayp, R_at ty q qx arrayp xs)%I
      (q in scope cQp_scope, qx in scope cQp_scope).

    Section with_cpp.
      Context `{Σ : cpp_logic, σ : genv}.
      Context (ty : type).

      #[local] Abbreviation initializer_list := (N ty) (only parsing).
      #[local] Abbreviation spineR q arrayp n := (initializer_listR ty q arrayp n).

      (** <<constexpr initializer_list() noexcept;>>

          <https://eel.is/c++draft/support.initlist.cons> -- an empty list. The
          backing array is empty, so there is no payload. *)
      Definition default_ctor :=
        specify.template.ctor initializer_list [] $
          \this this
          \post Exists arrayp, this |-> spineR (cQp.m 1) arrayp 0.
      #[global] Hint Opaque default_ctor : sl_opacity.
      #[global] Arguments default_ctor : simpl never.
      Definition SpecFor_default_ctor := RegisterSpec default_ctor.
      #[global] Existing Instance SpecFor_default_ctor.

      (** The (trivial) destructor.

          NOTE this is needed even though <<std::initializer_list>> owns
          nothing: a braced-init-list passed to a function creates a temporary
          <<initializer_list>>, and the enclosing full-expression destroys it.
          It consumes only the spine -- the backing array is a separate
          temporary with its own lifetime. *)
      Definition dtor :=
        specify.template.dtor initializer_list $
          \this this
          \pre{arrayp n} this |-> spineR (cQp.m 1) arrayp n
          \post emp.
      #[global] Hint Opaque dtor : sl_opacity.
      #[global] Arguments dtor : simpl never.
      Definition SpecFor_dtor := RegisterSpec dtor.
      #[global] Existing Instance SpecFor_dtor.

      (** <<constexpr size_t size() const noexcept;>>

          <https://eel.is/c++draft/support.initlist.access> *)
      Definition size :=
        let qf := function_qualifiers.Nc in
        specify.template.method initializer_list "size" qf Tsize_t [] $
          \this this
          \prepost{q arrayp n} this |-> spineR q arrayp n
          \post[Vn n] emp.
      #[global] Hint Opaque size : sl_opacity.
      #[global] Arguments size : simpl never.
      Definition SpecFor_size := RegisterSpec size.
      #[global] Existing Instance SpecFor_size.

      (** <<constexpr const E* begin() const noexcept;>>

          <https://eel.is/c++draft/support.initlist.access> *)
      Definition begin :=
        let qf := function_qualifiers.Nc in
        specify.template.method initializer_list "begin" qf (Tptr (Tconst ty)) [] $
          \this this
          \prepost{q arrayp n} this |-> spineR q arrayp n
          \post[Vptr arrayp] emp.
      #[global] Hint Opaque begin : sl_opacity.
      #[global] Arguments begin : simpl never.
      Definition SpecFor_begin := RegisterSpec begin.
      #[global] Existing Instance SpecFor_begin.

      (** <<constexpr const E* end() const noexcept;>>

          <https://eel.is/c++draft/support.initlist.access>: one past the last
          element, i.e. [begin() + size()]. *)
      Definition end_ :=
        let qf := function_qualifiers.Nc in
        specify.template.method initializer_list "end" qf (Tptr (Tconst ty)) [] $
          \this this
          \prepost{q arrayp n} this |-> spineR q arrayp n
          \post[Vptr (arrayp .[ ty ! Z.of_N n ])] emp.
      #[global] Hint Opaque end_ : sl_opacity.
      #[global] Arguments end_ : simpl never.
      Definition SpecFor_end_ := RegisterSpec end_.
      #[global] Existing Instance SpecFor_end_.

      Definition specs := default_ctor ** dtor ** size ** begin ** end_.
      #[global] Hint Opaque specs : typeclass_instances sl_opacity.
      #[only(knowledge)] derive specs.
    End with_cpp.
  NES.End initializer_list.
NES.End std.
