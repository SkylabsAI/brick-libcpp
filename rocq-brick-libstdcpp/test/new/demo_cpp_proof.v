Require Import bluerock.auto.cpp.prelude.proof.
Require Import bluerock.cpp.stdlib.new.pred.

Require Import bluerock.cpp.stdlib.new.spec_exc.
Require Import bluerock.cpp.stdlib.new.hints.
Require bluerock.cpp.stdlib.test.new.demo_cpp.

Section with_cpp.
  Context `{Σ : cpp_logic} `{MOD : demo_cpp.source ⊧ σ}.

  cpp.spec "test_new()" with
    (\post{p}[Vptr p]
       p |-> (intR 1$m 0 ** alloc.token "int" 4 1)).

  Lemma test_new_ok : verify[demo_cpp.source] "test_new()".
  Proof. verify_spec; go. Qed.

  cpp.spec "test_delete(int* )" with
    (\arg{p} "p" (Vptr p)
     \pre{v} p |-> (intR 1$m v ** alloc.token "int" 4 1)
     \post emp).

  Lemma test_delete_ok : verify[demo_cpp.source] "test_delete(int* )".
  Proof.
    verify_spec.
    go; case_bool_decide; go. (* TODO: improve automation *)
  Qed.

  cpp.spec "test_new_delete()" with
    (\post emp).

  Lemma test_new_delete_ok : verify[demo_cpp.source] "test_new_delete()".
  Proof. verify_spec; go. Qed.

End with_cpp.
