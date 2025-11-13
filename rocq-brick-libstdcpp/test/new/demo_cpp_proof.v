Require Import bluerock.auto.cpp.prelude.proof.
Require Import bluerock.brick.libstdcpp.new.pred.

Require Import bluerock.brick.libstdcpp.new.spec_exc.
Require Import bluerock.brick.libstdcpp.new.hints.
Require bluerock.brick.libstdcpp.test.new.demo_cpp.

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.

  Import linearity.

  cpp.spec "test_new()" from demo_cpp.source with
    (\post{p}[Vptr p]
       p |-> (intR 1$m 0 ** alloc.tokenR "int" 1)).

  Lemma test_new_ok : verify[demo_cpp.source] "test_new()".
  Proof. verify_spec; go. Qed.

  cpp.spec "test_delete(int* )" from demo_cpp.source with
    (\arg{p} "p" (Vptr p)
     \pre{v} p |-> (intR 1$m v ** alloc.tokenR "int" 1)
     \post emp).

  Lemma test_delete_ok : verify[demo_cpp.source] "test_delete(int* )".
  Proof.
    verify_spec.
    go; case_bool_decide; go.
  Qed.

  cpp.spec "test_new_delete()" from demo_cpp.source with
    (\post emp).

  Lemma test_new_delete_ok : verify[demo_cpp.source] "test_new_delete()".
  Proof. verify_spec; go. Qed.

  cpp.spec "test_new_array()" from demo_cpp.source with
    (\post{p}[Vptr p]
      p |-> (arrayLR "int" 0 2 (fun z => intR 1$m z) [1; 2]%Z **
      alloc.tokenR "int[2]" 1)
    ).

  cpp.spec "test_delete_array(int* )" from demo_cpp.source with
    (\arg{p} "p" (Vptr p)
     \pre p |-> (arrayLR "int" 0 2 (fun z => intR 1$m z) [1; 2]%Z **
                 alloc.tokenR "int[2]" 1)
     \post emp
    ).

  cpp.spec "test_new_delete_array()" from demo_cpp.source with
    (\post emp).

  Lemma test_delete_array_ok : verify[demo_cpp.source] "test_delete_array(int* )".
  Proof.
    verify_spec; go.
    case_bool_decide; try by go.
    go.
    case_bool_decide.
    { go. rewrite H. go. exfalso; lia. }
    { go. }
  Qed.

  (** The C++ standard recommends <<262144 <= SIZE_MAX>>.  *)
  Axiom Cpp_SIZE_MAX : (262144 <= SIZE_MAX)%N.

  Lemma test_new_array_ok : verify[demo_cpp.source] "test_new_array()".
  Proof.
    verify_spec.
    go.
    { exfalso.
      generalize Cpp_SIZE_MAX. lia. }
    { normalize_ptrs.
      rewrite Z.add_opp_diag_r. normalize_ptrs. go. }
  Qed.

  Lemma test_new_delete_array_ok : verify[demo_cpp.source] "test_new_delete_array()".
  Proof.
    verify_spec; go.
    normalize_ptrs.
    rewrite Z.add_opp_diag_r. normalize_ptrs.
    go.
  Qed.

End with_cpp.
