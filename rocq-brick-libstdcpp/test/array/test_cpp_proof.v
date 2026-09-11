(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.auto.cpp.prelude.test.

Require Import skylabs.cpp.string.

Require Import skylabs.brick.libstdcpp.array.spec.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.test.array.test_cpp.
(**
   Smoke tests for [std.array]. Every wrapper below is verified against the same
   set of template specifications, instantiated at <<std::array<int, 3> >>,
   <<std::array<unsigned, 5> >>, the nested <<std::array<std::array<int, 2>, 4> >>
   and the zero-length <<std::array<int, 0> >>.
 *)

Section with_cpp.
  Context `{Σ : cpp_logic} `{MOD : source ⊧ σ}.

  #[local] Open Scope Z_scope.

  (** Pointer arithmetic on the raw-pointer iterators of <<std::array>> produces
      nested offsets such as <<.[int ! 3].[int ! -1]>>; [normalize_ptr] folds them. *)
  Import normalize.normalize_ptr.

  Definition sum (xs : list Z) : Z := foldr Z.add 0 xs.
  #[global] Arguments sum !_ / : simpl nomatch.

  (** ** Capacity

      <<size>>, <<max_size>> and <<empty>> are fixed by the type. *)

  cpp.spec "Size(const std::array<int, 3ul>&)" as size_spec with
    (\arg{ap} "a" (Vref ap)
     \prepost{q xs} ap |-> std.array.R "int" 3 q xs
     \post[Vint 3] emp).

  Lemma size_ok : verify[ source ] size_spec.
  Proof using MOD. verify_spec; go. Qed.

  cpp.spec "MaxSize(const std::array<int, 3ul>&)" as max_size_spec with
    (\arg{ap} "a" (Vref ap)
     \prepost{q xs} ap |-> std.array.R "int" 3 q xs
     \post[Vint 3] emp).

  Lemma max_size_ok : verify[ source ] max_size_spec.
  Proof using MOD. verify_spec; go. Qed.

  cpp.spec "Empty(const std::array<int, 3ul>&)" as empty_spec with
    (\arg{ap} "a" (Vref ap)
     \prepost{q xs} ap |-> std.array.R "int" 3 q xs
     \post[Vbool false] emp).

  Lemma empty_ok : verify[ source ] empty_spec.
  Proof using MOD. verify_spec; go. Qed.

  (** ** Element access *)

  cpp.spec "Get(const std::array<int, 3ul>&, unsigned long)" as get_spec with
    (\arg{ap} "a" (Vref ap)
     \arg{i} "i" (Vint i)
     \require 0 ≤ i < 3
     \prepost{q xs} ap |-> std.array.R "int" 3 q xs
     \post[Vint (xs !!! i)] emp).

  Lemma get_ok : verify[ source ] get_spec.
  Proof using MOD. verify_spec; go. Qed.

  (** Writing through <<operator[]>> is stated with the tight footprint the
      specification is designed for: the spine plus the single element being
      written, rather than the whole array. *)
  cpp.spec "Set(std::array<int, 3ul>&, unsigned long, int)" as set_spec with
    (\arg{ap} "a" (Vref ap)
     \arg{i} "i" (Vint i)
     \arg{v} "v" (Vint v)
     \require 0 ≤ i < 3
     \prepost{q} ap |-> std.array.spineR "int" 3 q
     \let basep := ap ,, std.array.elems "int" 3
     \pre{x} basep .[ "int" ! i ] |-> intR 1$m x
     \post   basep .[ "int" ! i ] |-> intR 1$m v).

  Lemma set_ok : verify[ source ] set_spec.
  Proof using MOD. verify_spec; go. Qed.

  (** Only the in-range path of <<at>> is specified; see [std.array]. *)
  cpp.spec "GetAt(const std::array<int, 3ul>&, unsigned long)" as get_at_spec with
    (\arg{ap} "a" (Vref ap)
     \arg{i} "i" (Vint i)
     \require 0 ≤ i < 3
     \prepost{q xs} ap |-> std.array.R "int" 3 q xs
     \post[Vint (xs !!! i)] emp).

  Lemma get_at_ok : verify[ source ] get_at_spec.
  Proof using MOD. verify_spec; go. Qed.

  cpp.spec "Front(const std::array<int, 3ul>&)" as front_spec with
    (\arg{ap} "a" (Vref ap)
     \prepost{q xs} ap |-> std.array.R "int" 3 q xs
     \post[Vint (xs !!! 0)] emp).

  Lemma front_ok : verify[ source ] front_spec.
  Proof using MOD. verify_spec; go. Qed.

  cpp.spec "Back(const std::array<int, 3ul>&)" as back_spec with
    (\arg{ap} "a" (Vref ap)
     \with q xs x
     \prepost ap |-> std.array.R "int" 3 q (xs ++ [x])
     \post[Vint x] emp).

  Lemma back_ok : verify[ source ] back_spec.
  Proof using MOD. verify_spec; go. Qed.

  cpp.spec "Data(const std::array<int, 3ul>&)" as data_spec with
    (\arg{ap} "a" (Vref ap)
     \prepost{q xs} ap |-> std.array.R "int" 3 q xs
     \post[Vptr ((ap ,, std.array.elems "int" 3) .[ "int" ! 0 ])] emp).

  Lemma data_ok : verify[ source ] data_spec.
  Proof using MOD. verify_spec; go. Qed.

  (** ** Operations *)

  cpp.spec "Fill(std::array<int, 3ul>&, int)" as fill_spec with
    (\arg{ap} "a" (Vref ap)
     \arg{v} "v" (Vint v)
     \pre{xs} ap |-> std.array.R "int" 3 1$m xs
     \post    ap |-> std.array.R "int" 3 1$m (replicateZ 3 v)).

  Lemma fill_ok : verify[ source ] fill_spec.
  Proof using MOD. verify_spec; go. Qed.

  cpp.spec "Swap(std::array<int, 3ul>&, std::array<int, 3ul>&)" as swap_spec with
    (\arg{ap} "a" (Vref ap)
     \arg{bp} "b" (Vref bp)
     \with xs ys
     \pre  ap |-> std.array.R "int" 3 1$m xs ** bp |-> std.array.R "int" 3 1$m ys
     \post ap |-> std.array.R "int" 3 1$m ys ** bp |-> std.array.R "int" 3 1$m xs).

  Lemma swap_ok : verify[ source ] swap_spec.
  Proof using MOD. verify_spec; go. Qed.

  cpp.spec "AssignTo(std::array<int, 3ul>&, const std::array<int, 3ul>&)" as assign_to_spec with
    (\arg{dstp} "dst" (Vref dstp)
     \arg{srcp} "src" (Vref srcp)
     \prepost{q ys} srcp |-> std.array.R "int" 3 q ys
     \pre{xs} dstp |-> std.array.R "int" 3 1$m xs
     \post    dstp |-> std.array.R "int" 3 1$m ys).

  Lemma assign_to_ok : verify[ source ] assign_to_spec.
  Proof using MOD. verify_spec; go. Qed.

  (** <<std::move>> is only a cast; inline it so the move assignment is reached. *)
  cpp.spec "std::move<std::array<int, 3ul>&>(std::array<int, 3ul>&)" from source inline.

  (** [moved ty] is equality for the element types used here, so a moved-from
      <<std::array>> keeps its element values and only ownership moves. [go] leaves
      that as a payload [∃ x', [| x = x' |] ** Rp x'], which does not collapse to
      [Rp x] on its own; this is the rewrite that does it. *)
  #[local] Lemma moved_prim_elim (Rp : Z -> Rep) (x : Z) :
    (Exists x' : Z, [| x = x' |] ** Rp x') -|- Rp x.
  Proof.
    iSplit.
    - by iIntros "(%x' & -> & $)".
    - iIntros "H"; iExists x; iSplitR; [ by iIntros "!%" | iFrame ].
  Qed.

  cpp.spec "MoveTo(std::array<int, 3ul>&, std::array<int, 3ul>&)" as move_to_spec with
    (\arg{dstp} "dst" (Vref dstp)
     \arg{srcp} "src" (Vref srcp)
     \with xs ys
     \pre  dstp |-> std.array.R "int" 3 1$m xs ** srcp |-> std.array.R "int" 3 1$m ys
     \post dstp |-> std.array.R "int" 3 1$m ys ** srcp |-> std.array.R "int" 3 1$m ys).

  Lemma move_to_ok : verify[ source ] move_to_spec.
  Proof using MOD. verify_spec; go. setoid_rewrite moved_prim_elim. go. Qed.

  (** ** Iterators

      <<std::array>>'s iterators are raw pointers in libstdc++, so they need no
      representation predicate of their own. *)

  cpp.spec "FirstViaBegin(const std::array<int, 3ul>&)" as first_via_begin_spec with
    (\arg{ap} "a" (Vref ap)
     \prepost{q xs} ap |-> std.array.R "int" 3 q xs
     \post[Vint (xs !!! 0)] emp).

  Lemma first_via_begin_ok : verify[ source ] first_via_begin_spec.
  Proof using MOD. verify_spec; go. Qed.

  cpp.spec "FirstViaCBegin(const std::array<int, 3ul>&)" as first_via_cbegin_spec with
    (\arg{ap} "a" (Vref ap)
     \prepost{q xs} ap |-> std.array.R "int" 3 q xs
     \post[Vint (xs !!! 0)] emp).

  Lemma first_via_cbegin_ok : verify[ source ] first_via_cbegin_spec.
  Proof using MOD. verify_spec; go. Qed.

  cpp.spec "CEnd(const std::array<int, 3ul>&)" as cend_spec with
    (\arg{ap} "a" (Vref ap)
     \prepost{q xs} ap |-> std.array.R "int" 3 q xs
     \post[Vptr ((ap ,, std.array.elems "int" 3) .[ "int" ! 3 ])] emp).

  Lemma cend_ok : verify[ source ] cend_spec.
  Proof using MOD. verify_spec; go. Qed.

  cpp.spec "LastViaEnd(const std::array<int, 3ul>&)" as last_via_end_spec with
    (\arg{ap} "a" (Vref ap)
     \with q xs x
     \prepost ap |-> std.array.R "int" 3 q (xs ++ [x])
     \post[Vint x] emp).

  Lemma last_via_end_ok : verify[ source ] last_via_end_spec.
  Proof using MOD.
    verify_spec; go.
    rewrite !o_sub_sub /=. go.
  Qed.

  (** <<std::array>>'s iterators are raw pointers, so a condition such as
      <<it != a.end()>> is a builtin pointer comparison between the first and
      last element addresses, [p .[ "int" ! 0 ]] and [p .[ "int" ! 3 ]].
      [wp_eval_ptr_neq] splits that into two obligations, and only one of them can
      be discharged today:

      - [ptr_comparable] between the two pointers. [ptr_comparable_valid_CX]
        (SkyLabsAI/auto#452) proves it. It is passed explicitly because, unlike
        [ptr_comparable_cstringR], it is not registered in a hint database.
      - the value of the comparison, which [wp_eval_ptr_neq] states as
        [bool_decide (p1 <> p2)]. Deciding it means going from pointer equality
        back to index equality, which holds only where the pointers have addresses
        -- and [valid_ptr] does not give that. [auto]'s [refine1_offset] records
        exactly this gap: it is a [Refine1 false true], i.e. complete but not
        sound, and is registered only for <<unsigned char>>.

      So closing SkyLabsAI/auto#451 needs more than the merged hint, and the loop
      below still iterates by index. The <<Fail Qed>> pins the one remaining
      obligation and starts failing once it is closed. *)

  cpp.spec "BeginIsNotEnd(const std::array<int, 3ul>&)" as begin_is_not_end_spec with
    (\arg{ap} "a" (Vref ap)
     \prepost{q xs} ap |-> std.array.R "int" 3 q xs
     \post[Vbool true] emp).

  Lemma begin_is_not_end_ok : verify[ source ] begin_is_not_end_spec.
  Proof using MOD. verify_spec; go using ptr_comparable_valid_CX. Fail Qed. Abort.

  (** ** Iterating over an array

      The loop invariant keeps the yet-to-be-summed suffix [k, 5) of the array, in
      the style of the <<std::vector>> smoke tests. *)

  cpp.spec "SumIndexed(const std::array<unsigned int, 5ul>&)" as sum_indexed_spec with
    (\arg{ap} "a" (Vref ap)
     \prepost{q xs} ap |-> std.array.R "unsigned" 5 q xs
     \post[Vint (trim 32 (sum xs))] emp).

  Lemma sum_indexed_ok : verify[ source ] sum_indexed_spec.
  Proof using MOD.
    verify_spec; go.
    wp_for (fun _ =>
      \with k
      \require 0 ≤ k ≤ 5
      \prepost ap |-> std.array.spineR "unsigned int" 5 q
      \prepost a_addr |-> refR<"std::array<unsigned int, 5ul>"> 1$m ap
      \prepost{ys} (ap ,, std.array.elems "unsigned int" 5)
                |-> array_sliceR "unsigned int" k 5 (fun v => uintR q v) ys
      \pre     i_addr |-> ulongR 1$m k
      \pre{r}  r_addr |-> uintR 1$m r
      \post
        r_addr |-> uintR 1$m (trim 32 (r + sum ys)) **
        i_addr |-> ulongR 1$m 5).
    iExists 0, xs, 0. go.
    wp_if.
    all: go.
  Qed.

  (** ** Other instantiations

      The same template specifications cover a different element type and extent,
      and <<std::array>> nested inside itself. *)

  cpp.spec "GetU(const std::array<unsigned int, 5ul>&, unsigned long)" as get_u_spec with
    (\arg{ap} "a" (Vref ap)
     \arg{i} "i" (Vint i)
     \require 0 ≤ i < 5
     \prepost{q xs} ap |-> std.array.R "unsigned" 5 q xs
     \post[Vint (xs !!! i)] emp).

  Lemma get_u_ok : verify[ source ] get_u_spec.
  Proof using MOD. verify_spec; go. Qed.

  cpp.spec "SizeU(const std::array<unsigned int, 5ul>&)" as size_u_spec with
    (\arg{ap} "a" (Vref ap)
     \prepost{q xs} ap |-> std.array.R "unsigned" 5 q xs
     \post[Vint 5] emp).

  Lemma size_u_ok : verify[ source ] size_u_spec.
  Proof using MOD. verify_spec; go. Qed.

  cpp.spec "GetNested(const std::array<std::array<int, 2ul>, 4ul>&, unsigned long, unsigned long)"
    as get_nested_spec with
    (\arg{ap} "a" (Vref ap)
     \arg{i} "i" (Vint i)
     \arg{j} "j" (Vint j)
     \require 0 ≤ i < 4
     \require 0 ≤ j < 2
     \prepost{q xss} ap |-> std.array.R (std.array.T "int" 2) 4 q xss
     \post[Vint ((xss !!! i) !!! j)] emp).

  Lemma get_nested_ok : verify[ source ] get_nested_spec.
  Proof using MOD. verify_spec; go. Qed.

  (** ** Constructing an array

      Every client above receives its array by reference, so none of them forces
      [std.array.R] to be inhabited. These do: each builds a fresh array from an
      existing one and then reads it back, through the copy and the move
      constructor, at two instantiations. *)

  cpp.spec "CopyThenGet(const std::array<int, 3ul>&, unsigned long)"
    as copy_then_get_spec with
    (\arg{ap} "a" (Vref ap)
     \arg{i} "i" (Vint i)
     \require 0 ≤ i < 3
     \prepost{q xs} ap |-> std.array.R "int" 3 q xs
     \post[Vint (xs !!! i)] emp).

  Lemma copy_then_get_ok : verify[ source ] copy_then_get_spec.
  Proof using MOD. verify_spec; go. Qed.

  cpp.spec "CopyThenGetU(const std::array<unsigned int, 5ul>&, unsigned long)"
    as copy_then_get_u_spec with
    (\arg{ap} "a" (Vref ap)
     \arg{i} "i" (Vint i)
     \require 0 ≤ i < 5
     \prepost{q xs} ap |-> std.array.R "unsigned" 5 q xs
     \post[Vint (xs !!! i)] emp).

  Lemma copy_then_get_u_ok : verify[ source ] copy_then_get_u_spec.
  Proof using MOD. verify_spec; go. Qed.

  cpp.spec "std::move<std::array<unsigned int, 5ul>&>(std::array<unsigned int, 5ul>&)"
    from source inline.

  (** As in [move_to_ok], the moved-from array keeps its element values;
      [moved_prim_elim] collapses the leftover existential. *)
  cpp.spec "MoveThenGet(std::array<int, 3ul>&, unsigned long)"
    as move_then_get_spec with
    (\arg{ap} "a" (Vref ap)
     \arg{i} "i" (Vint i)
     \require 0 ≤ i < 3
     \prepost{xs} ap |-> std.array.R "int" 3 1$m xs
     \post[Vint (xs !!! i)] emp).

  Lemma move_then_get_ok : verify[ source ] move_then_get_spec.
  Proof using MOD. verify_spec; go. setoid_rewrite moved_prim_elim. go. Qed.

  cpp.spec "MoveThenGetU(std::array<unsigned int, 5ul>&, unsigned long)"
    as move_then_get_u_spec with
    (\arg{ap} "a" (Vref ap)
     \arg{i} "i" (Vint i)
     \require 0 ≤ i < 5
     \prepost{xs} ap |-> std.array.R "unsigned" 5 1$m xs
     \post[Vint (xs !!! i)] emp).

  Lemma move_then_get_u_ok : verify[ source ] move_then_get_u_spec.
  Proof using MOD. verify_spec; go. setoid_rewrite moved_prim_elim. go. Qed.

  (** ** Brace initialization

      Aggregate initialization calls no constructor ([array.overview]): the AST
      carries an [Einitlist] rather than an [Econstructor], so these clients never
      reach [std.array]'s constructor specifications. The representation predicate
      has to come out of BRiCk's initialization automation instead, which checks
      [std.array.R] against libstdc++'s layout rather than against an assumed
      specification. *)

  cpp.spec "BraceInitThenGet(unsigned long)" as brace_init_then_get_spec with
    (\arg{i} "i" (Vint i)
     \require 0 ≤ i < 3
     \post[Vint ([1; 2; 3] !!! i)] emp).

  Lemma brace_init_then_get_ok : verify[ source ] brace_init_then_get_spec.
  Proof using MOD. verify_spec; go. Qed.

  cpp.spec "BraceInitAssignmentThenGet(unsigned long)" as brace_init_assignment_then_get_spec with
    (\arg{i} "i" (Vint i)
     \require 0 ≤ i < 3
     \post[Vint ([1; 2; 3] !!! i)] emp).

  Lemma brace_init_assignment_then_get_ok : verify[ source ] brace_init_assignment_then_get_spec.
  Proof using MOD. verify_spec; go. Qed.

  cpp.spec "BraceInitThenGetU(unsigned long)" as brace_init_then_get_u_spec with
    (\arg{i} "i" (Vint i)
     \require 0 ≤ i < 5
     \post[Vint ([1; 2; 3; 4; 5] !!! i)] emp).

  Lemma brace_init_then_get_u_ok : verify[ source ] brace_init_then_get_u_spec.
  Proof using MOD. verify_spec; go. Qed.

  (** LIMITATION: a short initializer list value-initializes the remaining
      elements, which the AST records as an [Einitlist] carrying a filler
      ([Eimplicit_init]). The initialization automation does not handle that form
      yet, so this is pinned rather than proved. *)
  cpp.spec "BraceInitPartialThenGet(unsigned long)" as brace_init_partial_then_get_spec with
    (\arg{i} "i" (Vint i)
     \require 0 ≤ i < 3
     \post[Vint ([1; 0; 0] !!! i)] emp).

  Lemma brace_init_partial_then_get_ok : verify[ source ] brace_init_partial_then_get_spec.
  Proof using MOD. verify_spec; go. Fail Qed. Abort.

  (** <<array<int, 3> a{}>> value-initializes every element, unlike the omitted
      default constructor; see the LIMITATION in [std.array]. *)
  cpp.spec "BraceInitValueThenGet()" as brace_init_value_then_get_spec with
    (\post[Vint 0] emp).

  (** Value initialization goes through [primR] rather than through the element
      type's [BundledRep], hence the explicit hint. The index is a literal here:
      with a symbolic one the leftover total lookup ends up in the premise of a
      wand, where the [Normalize] hint that handles it elsewhere cannot reach it. *)
  Lemma brace_init_value_then_get_ok : verify[ source ] brace_init_value_then_get_spec.
  Proof using MOD. verify_spec; go using prim.primR_aggressiveC. Qed.

  cpp.spec "BraceInitNestedThenGet(unsigned long, unsigned long)"
    as brace_init_nested_then_get_spec with
    (\arg{i} "i" (Vint i)
     \arg{j} "j" (Vint j)
     \require 0 ≤ i < 2
     \require 0 ≤ j < 2
     \post[Vint (([[1; 2]; [3; 4]] !!! i) !!! j)] emp).

  (** LIMITATION: the nested aggregate initializer is an [Einitlist] of
      [Einitlist]s, which the initialization automation does not handle yet. Note
      that [get_nested_ok] above does verify reads of a nested array, so it is the
      initialization rather than [std.array.R] that is missing here. *)
  Lemma brace_init_nested_then_get_ok : verify[ source ] brace_init_nested_then_get_spec.
  Proof using MOD. verify_spec; go. Fail Qed. Abort.

  (** ** Remaining entry points *)

  cpp.spec "test(bool)" as test_spec with
    (\arg "b" (Vbool true)
     \post emp).

  Lemma test_ok : verify[ source ] test_spec.
  Proof using MOD. verify_spec; go. Qed.

  cpp.spec "main()" as main_spec with (\post[Vint 0] emp).

  Lemma main_ok : verify[ source ] main_spec.
  Proof using MOD. verify_spec; go. Qed.


  (** ** The zero-length instantiation

      <<std::array<int, 0> >> is only partly well defined; see the LIMITATION in
      [std.array]. These clients cover the members that do have a meaning at zero.
      <<operator[]>>, <<front>> and <<back>> are absent by design: they violate a
      hardened precondition ([sequence.reqmts]) and carry [0 < n], so no client can
      use them. *)

  cpp.spec "Size0(const std::array<int, 0ul>&)" as size0_spec with
    (\arg{ap} "a" (Vref ap)
     \prepost{q} ap |-> std.array.spineR "int" 0 q
     \post[Vint 0] emp).

  Lemma size0_ok : verify[ source ] size0_spec.
  Proof using MOD. verify_spec; go. Qed.

  cpp.spec "Empty0(const std::array<int, 0ul>&)" as empty0_spec with
    (\arg{ap} "a" (Vref ap)
     \prepost{q} ap |-> std.array.spineR "int" 0 q
     \post[Vbool true] emp).

  Lemma empty0_ok : verify[ source ] empty0_spec.
  Proof using MOD. verify_spec; go. Qed.

  (** [array.zero] leaves the value of <<data()>> unspecified; libstdc++ returns a
      null pointer and [std.array] commits to that. *)
  cpp.spec "Data0(const std::array<int, 0ul>&)" as data0_spec with
    (\arg{ap} "a" (Vref ap)
     \prepost{q} ap |-> std.array.spineR "int" 0 q
     \post[Vptr nullptr] emp).

  Lemma data0_ok : verify[ source ] data0_spec.
  Proof using MOD. verify_spec; go. Qed.

  (** <<begin() == end()>> is what [array.zero] does guarantee, and it is the reason
      to pin the value at all. *)
  cpp.spec "BeginIsEnd0(const std::array<int, 0ul>&)" as begin_is_end0_spec with
    (\arg{ap} "a" (Vref ap)
     \prepost{q} ap |-> std.array.spineR "int" 0 q
     \post[Vbool true] emp).

  Lemma begin_is_end0_ok : verify[ source ] begin_is_end0_spec.
  Proof using MOD. verify_spec; go. Qed.

  (** <<fill>> and <<swap>> degenerate to no-ops at zero ([array.members]). *)
  cpp.spec "Fill0(std::array<int, 0ul>&, int)" as fill0_spec with
    (\arg{ap} "a" (Vref ap)
     \arg{v} "v" (Vint v)
     \pre  ap |-> std.array.R "int" 0 1$m []
     \post ap |-> std.array.R "int" 0 1$m []).

  Lemma fill0_ok : verify[ source ] fill0_spec.
  Proof using MOD. verify_spec; go. Qed.

  cpp.spec "Swap0(std::array<int, 0ul>&, std::array<int, 0ul>&)" as swap0_spec with
    (\arg{ap} "a" (Vref ap)
     \arg{bp} "b" (Vref bp)
     \pre  ap |-> std.array.R "int" 0 1$m [] ** bp |-> std.array.R "int" 0 1$m []
     \post ap |-> std.array.R "int" 0 1$m [] ** bp |-> std.array.R "int" 0 1$m []).

  Lemma swap0_ok : verify[ source ] swap0_spec.
  Proof using MOD. verify_spec; go. Qed.

  (** ** Linking

      The clients above are proved against the specifications registered by
      [std.array]; the bundles [std.array.specs] provide exactly those. *)

  Definition size_B := [LINK] size_ok.
  Definition max_size_B := [LINK] max_size_ok.
  Definition empty_B := [LINK] empty_ok.
  Definition get_B := [LINK] get_ok.
  Definition set_B := [LINK] set_ok.
  Definition get_at_B := [LINK] get_at_ok.
  Definition front_B := [LINK] front_ok.
  Definition back_B := [LINK] back_ok.
  Definition data_B := [LINK] data_ok.
  Definition fill_B := [LINK] fill_ok.
  Definition swap_B := [LINK] swap_ok.
  Definition assign_to_B := [LINK] assign_to_ok.
  Definition move_to_B := [LINK] move_to_ok.
  Definition first_via_begin_B := [LINK] first_via_begin_ok.
  Definition first_via_cbegin_B := [LINK] first_via_cbegin_ok.
  Definition cend_B := [LINK] cend_ok.
  Definition last_via_end_B := [LINK] last_via_end_ok.
  Definition sum_indexed_B := [LINK] sum_indexed_ok.
  Definition get_u_B := [LINK] get_u_ok.
  Definition size_u_B := [LINK] size_u_ok.
  Definition get_nested_B := [LINK] get_nested_ok.
  Definition copy_then_get_B := [LINK] copy_then_get_ok.
  Definition copy_then_get_u_B := [LINK] copy_then_get_u_ok.
  Definition move_then_get_B := [LINK] move_then_get_ok.
  Definition move_then_get_u_B := [LINK] move_then_get_u_ok.
  Definition brace_init_then_get_B := [LINK] brace_init_then_get_ok.
  Definition brace_init_assignment_then_get_B := [LINK] brace_init_assignment_then_get_ok.
  Definition brace_init_then_get_u_B := [LINK] brace_init_then_get_u_ok.
  Definition brace_init_value_then_get_B := [LINK] brace_init_value_then_get_ok.
  Definition size0_B := [LINK] size0_ok.
  Definition empty0_B := [LINK] empty0_ok.
  Definition data0_B := [LINK] data0_ok.
  Definition begin_is_end0_B := [LINK] begin_is_end0_ok.
  Definition fill0_B := [LINK] fill0_ok.
  Definition swap0_B := [LINK] swap0_ok.
  Definition test_B := [LINK] test_ok.
  Definition main_B := [LINK] main_ok.

  #[local] Hint Resolve
    size_B max_size_B empty_B get_B set_B get_at_B front_B back_B data_B
    fill_B swap_B assign_to_B move_to_B first_via_begin_B first_via_cbegin_B
    cend_B last_via_end_B sum_indexed_B get_u_B size_u_B get_nested_B
    copy_then_get_B copy_then_get_u_B move_then_get_B move_then_get_u_B
    brace_init_then_get_B brace_init_assignment_then_get_B
    brace_init_then_get_u_B brace_init_value_then_get_B
    size0_B empty0_B data0_B begin_is_end0_B fill0_B swap0_B
    test_B main_B : sl_opacity.

  Definition specs :=
    size_spec ** max_size_spec ** empty_spec **
    get_spec ** set_spec ** get_at_spec ** front_spec ** back_spec ** data_spec **
    fill_spec ** swap_spec ** assign_to_spec ** move_to_spec **
    first_via_begin_spec ** first_via_cbegin_spec ** cend_spec ** last_via_end_spec **
    sum_indexed_spec **
    get_u_spec ** size_u_spec ** get_nested_spec **
    copy_then_get_spec ** copy_then_get_u_spec **
    move_then_get_spec ** move_then_get_u_spec **
    brace_init_then_get_spec ** brace_init_assignment_then_get_spec **
    brace_init_then_get_u_spec ** brace_init_value_then_get_spec **
    size0_spec ** empty0_spec ** data0_spec ** begin_is_end0_spec **
    fill0_spec ** swap0_spec **
    test_spec ** main_spec.

  (** Every client above is discharged by instantiations of the library bundle
      [std.array.specs] plus <<cassert>>: nothing else about <<std::array>> is
      needed, and nothing in the bundle is missing. *)

  Lemma specs_ok :
    denoteModule source **
    □ ▷ ( std.array.specs "int" 0 **
          std.array.specs "int" 2 **
          std.array.specs "int" 3 **
          std.array.specs "unsigned" 5 **
          std.array.specs (std.array.T "int" 2) 4 **
          std.cassert.specs )
    |-- specs.
  Proof using MOD.
    rewrite /specs /std.array.specs /std.cassert.specs.
    work.
  Qed.


End with_cpp.
