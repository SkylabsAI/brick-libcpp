(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.spec.
Require Export skylabs.cpp.slice.

Require Import skylabs.cpp.spec.concepts.
Require Import skylabs.cpp.spec.concepts.experimental.

Require Import skylabs.brick.libstdcpp.array.inc_array_cpp.
Require Import skylabs.brick.libstdcpp.array.inc_array_cpp_templates.

NES.Begin std.
  #[local] Open Scope Z_scope.

  NES.Begin array.
    (**
       Module [std.array] specifies <<std::array<ty, n> >> for an arbitrary element
       type [ty] and an arbitrary (positive) extent [n]: every definition below is a
       template specification in the sense of [specify.template], so a single
       specification applies to every instantiation.

       # Representation

       Unlike <<std::vector>>, a <<std::array>> stores its elements inline, so there is
       no separately allocated buffer and no capacity. The ownership of an array at [p]
       therefore splits into

       - [p |-> spineR ty n q], the <<struct>> identity of the array object, and
       - [p ,, elems ty n |-> array_sliceR ty 0 n Rpayload xs], the [n] element payloads,

       bundled as [p |-> R_gen ty n q Rpayload xs], with [p |-> R ty n q xs] using the
       element type's [BundledRep] as the payload. Splitting the two gives the same
       benefits as for <<std::vector>>: array automation applies to random access,
       specifications keep tight footprints, and a client may vary the representation
       of individual elements over time. See [std.vector] for the extended rationale.

       Because the element storage is at a fixed offset from the array object, the
       "base pointer" is [p ,, elems ty n] rather than a value stored in the object;
       <<data()>>, <<begin()>> and <<end()>> return pointers derived from it.

       # Supported surface

       - element access: <<operator[]>>, <<at>>, <<front>>, <<back>>, <<data>>
       - iterators: <<begin>>, <<end>>, <<cbegin>>, <<cend>>
       - capacity: <<size>>, <<max_size>>, <<empty>>
       - operations: <<fill>>, <<swap>>
       - special members: copy/move construction, copy/move assignment, destruction

       # Deliberate omissions

       LIMITATION: <<std::array<ty, 0> >> is covered only in part, because only part
         of it is well defined. At [n = 0]:

         - <<size>>, <<max_size>>, <<empty>>, <<fill>>, <<swap>> and the special
           members are well defined and are specified. <<fill>> and <<swap>> degenerate
           to no-ops ([array.members]), and the free <<swap>> is explicitly permitted
           even for non-swappable <<ty>> ([array.special]).
         - <<data>>, <<begin>>, <<end>>, <<cbegin>> and <<cend>> are well defined, but
           [array.zero] leaves their value unspecified and requires only that they
           agree. We commit to libstdc++'s null pointer; see the note on the
           pointer-returning members below.
         - <<operator[]>>, <<front>> and <<back>> violate a hardened precondition
           ([sequence.reqmts]), hence are undefined on a non-hardened implementation
           and terminate on a hardened one ([structure.specifications]). They carry
           [0 < n] individually and so are unusable, rather than wrong, at [n = 0].
         - <<at>> is well defined at [n = 0]: it throws <<out_of_range>>
           ([sequence.reqmts]). Exceptions are not modelled here so only the [0 < n]
           path is modeled here.

       LIMITATION: the reverse iterators <<rbegin>>, <<rend>>, <<crbegin>> and
         <<crend>> are omitted: they return <<std::reverse_iterator>>, which this
         library does not specify yet.

       LIMITATION: the default constructor and aggregate initialization are omitted.
         Default-initializing a <<std::array>> of trivially default constructible
         elements leaves them uninitialized while value-initialization zeroes them, and
         separating those two cases needs a triviality side-condition we cannot state
         yet. Aggregate initialization does not call a constructor and is handled by
         BRiCk's initialization automation rather than by a specification here.

       LIMITATION: exceptions are not modelled, so <<at>> is specified only on its
         in-range path even though it is defined to throw <<std::out_of_range>>
         otherwise. This matches the <<std::vector>> specification.

       LIMITATION: the non-member interface is omitted: <<operator==>>, the three-way
         comparison <<operator<=> >>, <<std::get>>, <<std::to_array>>, the
         <<std::swap>> overload, and the tuple interface (<<tuple_size>>,
         <<tuple_element>>).

       NOTE: because the iterators are raw pointers, a loop condition such as
         <<it != a.end()>> is a builtin pointer comparison between two distinct
         pointers into the same array. The current automation cannot discharge the
         resulting [ptr_comparable] side condition, so client loops over a
         <<std::array>> should iterate by index (<<a[i]>>) rather than by iterator.
         See the smoke tests in <<test/array>> for a verified index loop.

       Reference:
         - https://eel.is/c++draft/array
         - https://en.cppreference.com/w/cpp/container/array
     *)

    #[global] Abbreviation N ty n :=
      (Ninst "std::array" [Atype ty; Avalue (Eint n "unsigned long")]) (only parsing).
    #[global] Abbreviation T ty n := (Tnamed (N ty n)) (only parsing).

    (** <<std::array<ty, n>::size_type>>, i.e. <<std::size_t>>. *)
    #[global] Abbreviation size_type := ("unsigned long"%cpp_type) (only parsing).
    (** <<std::array<ty, n>::difference_type>>, i.e. <<std::ptrdiff_t>>.

        NOTE: this must be spelled with a builtin type name. The <<cpp_type>> notation
        has no <<ptrdiff_t>> (or <<size_t>>) keyword, so <<"ptrdiff_t">> parses as the
        named type [Tnamed (Nglobal (Nid "ptrdiff_t"))] rather than as an integer type,
        which matches nothing in the AST. Both spellings here are LP64-specific, as is
        the rest of this file. *)
    #[global] Abbreviation difference_type := ("long"%cpp_type) (only parsing).

    (** The offset from a <<std::array<ty, n> >> object to its element storage.

        NOTE: this is libstdc++-specific: <<_M_elems>> is the (only) data member of
        <<std::array>> in libstdc++, and it has type <<ty[n]>> whenever [n] is positive.

        At [n = 0] the member still exists, at offset 0, but its type is the empty
        <<struct>> <<__array_traits<ty, 0>::_Type>> rather than an array, so this offset
        does not denote element storage. Nothing below reads elements at [n = 0]:
        [R_gen]'s slice is empty there, and the pointer-returning members do not derive
        their result from this offset. *)
    #[global] Abbreviation elems ty n := (_field (N ty n .:: Nid "_M_elems")) (only parsing).
    (** [spineR ty n q] owns the shape of a <<std::array<ty, n> >> object: the
        <<struct>> identity that ties the inline element storage to the array object,
        but none of the element payloads.

        Because <<std::array>> stores its elements inline, the spine carries no data:
        for [0 < n] the address of the storage is [p ,, elems ty n] for an array at [p],
        and the number of elements is fixed by [n] (hence by the type).

        The [0 ≤ n] conjunct records that [n] models a <<std::size_t>> template
        argument. It is deliberately not [0 < n]: the zero-length case is partly well
        defined, so the members that have a meaning at [n = 0] are specified here, and
        the ones that do not carry [0 < n] themselves. See the LIMITATION on
        <<std::array<ty, 0> >> above. *)
    sl.lock
    Definition spineR `{Σ : cpp_logic} {σ : genv} (ty : type) (n : Z) (q : cQp.t) : Rep :=
      structR (N ty n) q ** [| 0 ≤ n |].
    #[only(lazy_unfold,type_ptr,cfractional,ascfractional,cfracvalid)] derive spineR.

    (** [R_gen ty n q Rpayload xs] owns a whole <<std::array<ty, n> >>: its spine
        together with its [n] elements [xs], each described by [Rpayload].

        Splitting the spine from the payload lets clients keep tight footprints and
        vary the representation of individual elements over time, exactly as for
        <<std::vector>>; see [std.vector] for the rationale. *)
    #[global] Abbreviation R_gen ty n q Rpayload xs :=
      (spineR ty n q ** elems ty n |-> array_sliceR ty 0 n Rpayload xs)%I
      (ty in scope cpp_type_scope, n in scope Z_scope, q in scope cQp_scope).

    (** [R ty n q xs] is the default ownership of a <<std::array<ty, n> >> holding [xs],
        using the [BundledRep] of [ty] for the elements. *)
    #[global] Abbreviation R ty n q xs := (R_gen ty n q (objR ty q) xs)
      (ty in scope cpp_type_scope, n in scope Z_scope, q in scope cQp_scope).

    (** A <<std::array<ty, n> >> is modelled by the list of its elements, so it can be
        used as the element type of another container (including another
        <<std::array>>). *)
    #[global] Instance array_BundledRep `{Σ : cpp_logic} {σ : genv} ty n `{!BundledRep ty V} :
      BundledRep (T ty n) (list V) := {| objR := fun q xs => R ty n q xs |}.

    (** Value-initializing a <<std::array<ty, n> >> value-initializes each element
        ([array.overview]); this is the model of <<std::array<ty, n>{} >>, and it is
        what containers of arrays use when they need a default element. *)
    #[global] Instance array_DefaultValue ty n `{!DefaultValue ty V} :
      DefaultValue (T ty n) (list V) :=
      {| default_val := replicateZ n (default_val ty) |}.

    (** Moving a <<std::array<ty, n> >> moves each element, so the moved-from array
        has the same length and its elements are element-wise moved-from. *)
    #[global] Instance array_MovedValue ty n `{!MovedValue ty V} :
      MovedValue (T ty n) (list V) :=
      {| moved := Forall2 (moved ty) |}.

    Section with_RepFor.
      Import rep.RepFor.
      Import RepScheme.

      #[global] Instance repfor `{Σ : cpp_logic} {σ : genv} ty n `(_ : BundledRep ty M) :
        rep.RepFor.C (T ty n)
          [ArgType.CFrac; ArgType.Model _]
          (λ q xs, R ty n q xs) := {}.
    End with_RepFor.

    Section with_cpp.
      Context `{Σ : cpp_logic, σ : genv}.
      Context (ty : type) (n : Z).

      #[local] Abbreviation array := (N ty n) (only parsing).	(** <<array<ty, n> >> *)
      #[local] Abbreviation arrayT := (Tnamed array) (only parsing).
      #[local] Abbreviation spineR q := (spineR ty n q).
      #[local] Abbreviation R q xs := (R ty n q xs).

      (** [basep this] is the address of the element storage of the array at [this]. It
          denotes element storage only when [0 < n]; see [elems]. *)
      #[local] Abbreviation basep this := (this ,, elems ty n).

      (** [beginp this] is the value of <<this->data()>>, <<this->begin()>> and
          <<this->cbegin()>>; [endp this] is the value of <<this->end()>> and
          <<this->cend()>>.

          For [0 < n] these are the address of the first element and the corresponding
          past-the-end pointer. For [n = 0] the standard requires only
          <<begin() == end() == unique value>> and leaves the value of <<data()>>
          unspecified ([array.zero]); libstdc++ returns a null pointer, because the
          conversion operator on its empty <<_M_elems>> stand-in is
          <<constexpr explicit operator ty*() const noexcept { return nullptr; }>>. We
          commit to that value, as this library does elsewhere for libstdc++
          representation choices.

          NOTE: both reduce to <<nullptr>> at [n = 0] without any pointer arithmetic,
          which is what lets a client conclude <<begin() == end()>> there. *)
      #[local] Abbreviation beginp this :=
        (if bool_decide (n = 0) then nullptr else (basep this) .[ ty ! 0 ]).
      #[local] Abbreviation endp this :=
        (if bool_decide (n = 0) then nullptr else (basep this) .[ ty ! n ]).

      (** At [n = 0] the two agree, for every [ty], which is exactly the property
          [array.zero] guarantees. This holds by construction rather than by any
          reasoning about pointers; it is stated so that a change to one of
          [beginp]/[endp] and not the other fails here rather than downstream.

          NOTE: the converse — that they differ when [0 < n] — is not provable from
          these definitions alone. It needs [same_address_o_sub_eq], i.e. that distinct
          indices into an array whose element type has positive size have distinct
          addresses. That is the same missing ingredient as the [ptr_comparable]
          cancellation hint for <<it != a.end()>>, so the two are worth doing
          together. *)
      Lemma beginp_endp_agree_at_zero (this : ptr) : n = 0 -> beginp this = endp this.
      Proof. by move=>->. Qed.

      (** <<size()>> and <<max_size()>> are [constexpr] and always return [n]. *)
      Definition size :=
        let qf := function_qualifiers.Nc in
        specify.template.method array "size" qf size_type [] $
          \this this
          \prepost{q} this |-> spineR q
          \post[Vint n] emp.
      #[global] Hint Opaque size : sl_opacity.
      #[global] Arguments size : simpl never.
      Definition SpecFor_size := RegisterSpec size.
      #[global] Existing Instance SpecFor_size.

      Definition max_size :=
        let qf := function_qualifiers.Nc in
        specify.template.method array "max_size" qf size_type [] $
          \this this
          \prepost{q} this |-> spineR q
          \post[Vint n] emp.
      #[global] Hint Opaque max_size : sl_opacity.
      #[global] Arguments max_size : simpl never.
      Definition SpecFor_max_size := RegisterSpec max_size.
      #[global] Existing Instance SpecFor_max_size.

      (** <<empty()>> is [constexpr]: it is [true] exactly for <<std::array<ty, 0> >>. *)
      Definition empty :=
        let qf := function_qualifiers.Nc in
        specify.template.method array "empty" qf Tbool [] $
          \this this
          \prepost{q} this |-> spineR q
          \post[Vbool (bool_decide (n = 0))] emp.
      #[global] Hint Opaque empty : sl_opacity.
      #[global] Arguments empty : simpl never.
      Definition SpecFor_empty := RegisterSpec empty.
      #[global] Existing Instance SpecFor_empty.

      (** <<operator[](i)>> requires [0 ≤ i < n]: out-of-range indices are undefined
          behaviour ([array.overview]). *)
      Definition subscript c :=
        let qf := function_qualifiers.mk c false Prvalue in
        specify.template.op array OOSubscript qf (Tref (Tconst_if c ty)) [size_type] $
          \this this
          \arg{i} "i" (Vint i)
          \prepost{q} this |-> spineR q
          \require 0 ≤ i < n
          \let elemp := (basep this) .[ ty ! i ]
          \post[Vref elemp] emp.
      #[global] Hint Opaque subscript : sl_opacity.
      #[global] Arguments subscript : simpl never.
      Definition SpecFor_subscript := RegisterSpec subscript.
      #[global] Existing Instance SpecFor_subscript.

      (** LIMITATION: this specification does not discuss exceptions, so <<at>> is
          specified only on its in-range path. Out of range, <<at>> throws
          <<std::out_of_range>> ([array.members]) rather than being undefined. *)
      Definition at_ c :=
        let qf := function_qualifiers.mk c false Prvalue in
        specify.template.method array "at" qf (Tref (Tconst_if c ty)) [size_type] $
          \this this
          \arg{i} "i" (Vint i)
          \prepost{q} this |-> spineR q
          \require 0 ≤ i < n
          \let elemp := (basep this) .[ ty ! i ]
          \post[Vref elemp] emp.
      #[global] Hint Opaque at_ : sl_opacity.
      #[global] Arguments at_ : simpl never.
      Definition SpecFor_at_ := RegisterSpec at_.
      #[global] Existing Instance SpecFor_at_.

      (** <<front()>> and <<back()>> carry the hardened precondition <<!empty()>>
          ([sequence.reqmts]), so on an empty array they are undefined on a
          non-hardened implementation and terminate on a hardened one
          ([structure.specifications]). Either way there is nothing to specify, hence
          the [0 < n] below.

          NOTE: C++17 said this directly in [array.zero]; that sentence is gone and the
          requirement now reaches <<array>> through the sequence container tables
          ([array.overview]). In libstdc++ both members are <<_M_elems[…]>>, and
          indexing the empty <<_M_elems>> stand-in is <<__builtin_trap()>>. *)
      Definition front c :=
        let qf := function_qualifiers.mk c false Prvalue in
        specify.template.method array "front" qf (Tref (Tconst_if c ty)) [] $
          \this this
          \prepost{q} this |-> spineR q
          \require 0 < n
          \let elemp := (basep this) .[ ty ! 0 ]
          \post[Vref elemp] emp.
      #[global] Hint Opaque front : sl_opacity.
      #[global] Arguments front : simpl never.
      Definition SpecFor_front := RegisterSpec front.
      #[global] Existing Instance SpecFor_front.

      Definition back c :=
        let qf := function_qualifiers.mk c false Prvalue in
        specify.template.method array "back" qf (Tref (Tconst_if c ty)) [] $
          \this this
          \prepost{q} this |-> spineR q
          \require 0 < n
          \let elemp := (basep this) .[ ty ! n - 1 ]
          \post[Vref elemp] emp.
      #[global] Hint Opaque back : sl_opacity.
      #[global] Arguments back : simpl never.
      Definition SpecFor_back := RegisterSpec back.
      #[global] Existing Instance SpecFor_back.

      (** In libstdc++ <<std::array>>'s <<iterator>> and <<const_iterator>> are the raw
          pointer types <<ty*>> and <<const ty*>>, so <<begin()>>, <<end()>> and
          <<data()>> all return plain pointers into the element storage and need no
          separate iterator representation predicate. *)
      Definition data c :=
        let qf := function_qualifiers.mk c false Prvalue in
        specify.template.method array "data" qf (Tptr (Tconst_if c ty)) [] $
          \this this
          \prepost{q} this |-> spineR q
          \post[Vptr (beginp this)] emp.
      #[global] Hint Opaque data : sl_opacity.
      #[global] Arguments data : simpl never.
      Definition SpecFor_data := RegisterSpec data.
      #[global] Existing Instance SpecFor_data.

      Definition begin_spec c :=
        let qf := function_qualifiers.mk c false Prvalue in
        specify.template.method array "begin" qf (Tptr (Tconst_if c ty)) [] $
          \this this
          \prepost{q} this |-> spineR q
          \post[Vptr (beginp this)] emp.
      #[global] Hint Opaque begin_spec : sl_opacity.
      #[global] Arguments begin_spec : simpl never.
      Definition SpecFor_begin_spec := RegisterSpec begin_spec.
      #[global] Existing Instance SpecFor_begin_spec.

      Definition end_spec c :=
        let qf := function_qualifiers.mk c false Prvalue in
        specify.template.method array "end" qf (Tptr (Tconst_if c ty)) [] $
          \this this
          \prepost{q} this |-> spineR q
          \post[Vptr (endp this)] emp.
      #[global] Hint Opaque end_spec : sl_opacity.
      #[global] Arguments end_spec : simpl never.
      Definition SpecFor_end_spec := RegisterSpec end_spec.
      #[global] Existing Instance SpecFor_end_spec.

      Definition cbegin_spec :=
        let qf := function_qualifiers.Nc in
        specify.template.method array "cbegin" qf (Tptr (Tconst ty)) [] $
          \this this
          \prepost{q} this |-> spineR q
          \post[Vptr (beginp this)] emp.
      #[global] Hint Opaque cbegin_spec : sl_opacity.
      #[global] Arguments cbegin_spec : simpl never.
      Definition SpecFor_cbegin_spec := RegisterSpec cbegin_spec.
      #[global] Existing Instance SpecFor_cbegin_spec.

      Definition cend_spec :=
        let qf := function_qualifiers.Nc in
        specify.template.method array "cend" qf (Tptr (Tconst ty)) [] $
          \this this
          \prepost{q} this |-> spineR q
          \post[Vptr (endp this)] emp.
      #[global] Hint Opaque cend_spec : sl_opacity.
      #[global] Arguments cend_spec : simpl never.
      Definition SpecFor_cend_spec := RegisterSpec cend_spec.
      #[global] Existing Instance SpecFor_cend_spec.

      Section with_element_rep.
        Context `{!BundledRep ty V}.

        (** <<fill(u)>> assigns [u] to every element ([array.fill]). *)
        Definition fill :=
          let qf := function_qualifiers.N in
          specify.template.method array "fill" qf Tvoid [Tref (Tconst ty)] $
            \this this
            \arg{vp} "u" (Vref vp)
            \prepost{q v} vp |-> objR ty q v
            \pre{xs} this |-> R (cQp.m 1) xs
            \post    this |-> R (cQp.m 1) (replicateZ n v).
        #[global] Hint Opaque fill : sl_opacity.
        #[global] Arguments fill : simpl never.
        Definition SpecFor_fill := RegisterSpec fill.
        #[global] Existing Instance SpecFor_fill.

        (** <<swap(other)>> exchanges the elements of the two arrays ([array.swap]).
            Unlike <<std::vector::swap>>, it is linear in [n] and does not exchange
            storage, so element addresses are unchanged on both sides. *)
        Definition swap :=
          let qf := function_qualifiers.N in
          specify.template.method array "swap" qf Tvoid [Tref arrayT] $
            \this this
            \arg{otherp} "other" (Vref otherp)
            \with xs ys
            \pre  this |-> R (cQp.m 1) xs ** otherp |-> R (cQp.m 1) ys
            \post this |-> R (cQp.m 1) ys ** otherp |-> R (cQp.m 1) xs.
        #[global] Hint Opaque swap : sl_opacity.
        #[global] Arguments swap : simpl never.
        Definition SpecFor_swap := RegisterSpec swap.
        #[global] Existing Instance SpecFor_swap.
      End with_element_rep.

      (** ** Special member functions

          <<std::array>> is an aggregate, so all of its special member functions are
          implicitly defined and act element-wise ([array.overview]). *)
      Section special_members.
        Context `{!BundledRep ty V}.

        Definition copy_ctor :=
          specify.template.ctor array [Tref (Tconst arrayT)] $
            \this this
            \arg{otherp} "other" (Vref otherp)
            \prepost{q__other xs} otherp |-> R q__other xs
            \post this |-> R (cQp.m 1) xs.
        #[global] Hint Opaque copy_ctor : sl_opacity.
        #[global] Arguments copy_ctor : simpl never.
        Definition SpecFor_copy_ctor := RegisterSpec copy_ctor.
        #[global] Existing Instance SpecFor_copy_ctor.

        Definition copy_assign :=
          let qf := function_qualifiers.N in
          specify.template.op array OOEqual qf (Tref arrayT) [Tref (Tconst arrayT)] $
            \this this
            \arg{otherp} "other" (Vref otherp)
            \prepost{q__other ys} otherp |-> R q__other ys
            \pre{xs}         this |-> R (cQp.m 1) xs
            \post[Vref this] this |-> R (cQp.m 1) ys.
        #[global] Hint Opaque copy_assign : sl_opacity.
        #[global] Arguments copy_assign : simpl never.
        Definition SpecFor_copy_assign := RegisterSpec copy_assign.
        #[global] Existing Instance SpecFor_copy_assign.

        Definition dtor :=
          specify.template.dtor array $
            \this this
            \pre{xs} this |-> R (cQp.m 1) xs
            \post emp.
        #[global] Hint Opaque dtor : sl_opacity.
        #[global] Arguments dtor : simpl never.
        Definition SpecFor_dtor := RegisterSpec dtor.
        #[global] Existing Instance SpecFor_dtor.
      End special_members.

      Section move_members.
        Context `{!BundledRep ty V, !MovedValue ty V}.

        (** [R_moved q xs] owns an array whose elements are each in the moved-from
            state corresponding to the matching element of [xs]. Moving a
            <<std::array>> moves the elements: it does not steal storage, so [other]
            keeps its size and its element addresses ([array.overview]). *)
        #[local] Abbreviation R_moved q xs :=
          (R_gen ty n q (fun x => moved_objR ty q x) xs)
          (q in scope cQp_scope).

        Definition move_ctor :=
          specify.template.ctor array [Trv_ref arrayT] $
            \this this
            \arg{otherp} "other" (Vref otherp)
            \pre{xs} otherp |-> R (cQp.m 1) xs
            \post*   otherp |-> R_moved (cQp.m 1) xs
            \post    this   |-> R (cQp.m 1) xs.
        #[global] Hint Opaque move_ctor : sl_opacity.
        #[global] Arguments move_ctor : simpl never.
        Definition SpecFor_move_ctor := RegisterSpec move_ctor.
        #[global] Existing Instance SpecFor_move_ctor.

        Definition move_assign :=
          let qf := function_qualifiers.N in
          specify.template.op array OOEqual qf (Tref arrayT) [Trv_ref arrayT] $
            \this this
            \arg{otherp} "other" (Vref otherp)
            \with xs ys
            \pre             otherp |-> R (cQp.m 1) ys
            \post*           otherp |-> R_moved (cQp.m 1) ys
            \pre             this   |-> R (cQp.m 1) xs
            \post[Vref this] this   |-> R (cQp.m 1) ys.
        #[global] Hint Opaque move_assign : sl_opacity.
        #[global] Arguments move_assign : simpl never.
        Definition SpecFor_move_assign := RegisterSpec move_assign.
        #[global] Existing Instance SpecFor_move_assign.
      End move_members.

      Section specs.
        Context `{!BundledRep ty V}.
        Context `{!MovedValue ty V}.

        #[local] Abbreviation MaybeConst spec := (spec true ** spec false).

        Definition specs :=
          size **
          max_size **
          empty **
          MaybeConst subscript **
          MaybeConst at_ **
          MaybeConst front **
          MaybeConst back **
          MaybeConst data **
          MaybeConst begin_spec **
          MaybeConst end_spec **
          cbegin_spec **
          cend_spec **
          fill **
          swap **
          copy_ctor **
          copy_assign **
          dtor **
          move_ctor **
          move_assign.
        #[global] Hint Opaque specs : typeclass_instances sl_opacity.
        #[only(knowledge)] derive specs.
      End specs.

    End with_cpp.

    Section instances_hints.
      Context `{Σ : cpp_logic} {σ : genv} (ty : type) (n : Z).

      (** Owning any part of an array's spine witnesses that [n] is a well-formed
          extent; see the note on [spineR]. *)
      #[global] Instance spineR_nonneg q : Observe [| 0 ≤ n |] (spineR ty n q).
      Proof. rewrite spineR.unlock. refine _. Qed.
    End instances_hints.

  NES.End array.

NES.End std.
