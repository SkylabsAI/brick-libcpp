Require Import bluerock.auto.cpp.proof.
Require Import bluerock.cpp.stdlib.allocator.spec.
Require Import bluerock.cpp.stdlib.cassert.spec.
Require Import bluerock.cpp.stdlib.vector.spec.
Require Import bluerock.cpp.stdlib.atomic.spec.
Require Import bluerock.cpp.stdlib.algorithms.spec.
Require Import bluerock.cpp.stdlib.new.spec_exc.
Require Import bluerock.brick.libcpp.newarr.spec_exc.
Require Import bluerock.brick.libcpp.newarr.hints.
Require Import bluerock.cpp.spec.concepts.
Require Import bluerock.cpp.spec.concepts.experimental.
Require Import bluerock.brick.libcpp.newarr.test_cpp.
Require Import bluerock.cpp.stdlib.new.hints.

Import linearity.
Disable Notation "::wpOperand".
Print new_delete.wp_operand_array_new_glob.
Section specsproofs.
  Context `{Σ : cpp_logic, MOD:test_cpp.module ⊧ σ}.

  Definition dynAllocatedR ty (base:ptr) : mpred :=
    Exists (bookKeepingLoc:ptr) (overhead:N),
      match (size_of _ ty) with
      | Some sz => bookKeepingLoc |-> pred.allocatedR 1 (overhead+sz)
      | None => False
      end **
      match ty with
      | Tint  => [| overhead = 0%N |]
      | _ =>  True (* TODO: this needs to be strengthened for many cases *)
      end
      **  (base |-> new_token.R 1
                {| new_token.alloc_ty := ty;
                   new_token.storage_ptr := bookKeepingLoc.["unsigned char" ! overhead];
                  new_token.overhead := overhead |}).
  
  cpp.spec "testnew()" as testnewspec with (
    \pre emp
    \post{p:ptr}[Vptr p] dynAllocatedR "int" p ** p |-> primR "int" 1 (Vint 1)
    ).

  Lemma prf: verify[module] testnewspec.
  Proof using MOD.
    verify_spec.
    go;[ego | ego |].
    unfold dynAllocatedR. go.
    ego.
    eagerUnifyU.
    normalize_ptrs.
    go.
  Qed.
  cpp.spec "testnewarr()" as testnewarrspec with
    (
      \pre emp
        \post{p:ptr}[Vptr p] dynAllocatedR "int[2]" p
        ** p |-> arrayR "int" (fun x => primR "int" 1 (Vint x)) [1;2]%Z
    ).
  
  Lemma prf3: verify[module] testnewarrspec.
  Proof using MOD. 
    verify_spec.
    go.
    unfold dynAllocatedR.
    go.
    iExists _.
    eagerUnifyU.
    go.
    simpl.
    rewrite arrayR_eq.
    unfold arrayR_def.
    go.
    rewrite arrR_eq.
    unfold arrR_def.
    go.
    simpl.
    ego.
    unfold dynAllocatedR.
    ego.
    rewrite arrayR_eq.
    unfold arrayR_def.
    go.
    rewrite arrR_eq.
    unfold arrR_def.
    go.
  Qed.

    
  cpp.spec "testnewdel()" as testnewdelspec with (
        \post emp).
  
  Opaque dynAllocatedR.
  
  Lemma prfdel: verify[module] testnewdelspec.
  Proof using MOD.
    verify_spec.
    go;[ego|].
    Transparent dynAllocatedR.
    go.
    case_bool_decide; Forward.rwHyps; try go;[].
    go.
    normalize_ptrs.
    go.
  Qed.
  
  cpp.spec "testnewarrdel()" as testnewarrdelspec with (
        \post emp).
  
  Lemma prf2del: verify[module] testnewarrdelspec.
  Proof using MOD.
    verify_spec.
    go;[ego|].
    Transparent dynAllocatedR.
    Search arrayR nullptr.
    go.
    rewrite arrayR_eq.
    unfold arrayR_def.
    go.
    rewrite arrR_eq.
    unfold arrR_def.
    go.
    case_bool_decide; subst; try go.
    assert ("int"%cpp_type = "int[2]"%cpp_type) as Hfalse by admit.
    (* _x_ |-> anyR "int[2]" 1$m *)
    (* It seems the delete wp or spec is horribly wrong for the case of delete [] *)
  Abort.

End specsproofs.
