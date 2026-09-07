(**
Tentative iostreams specs.

These are trace-based specifications, and there is a _wish_ to move to a
different style of specifications.

*)
Require Import skylabs.auto.cpp.prelude.proof.
Require Export skylabs.cpp.string.
Require Export skylabs.brick.libstdcpp.iostream.pred.
Require Export skylabs.brick.libstdcpp.iostream.itree_prop.

Require Import skylabs.brick.libstdcpp.iostream_trace.inc_iostream_cpp.

(*
Variant io_align : Set := left | right | internal.
Variant io_base : Set := dec | hex | oct.
Variant io_float : Set := fixed | scientific | hexfloat | defaultfloat.

Record ioflags : Set :=
{ boolalpha : bool
; showbase : bool
; showpoint : bool
; showpos : bool
; uppercase : bool
; align : io_align
; float : io_float
}.
*)

(* TODO: it probably makes sense to separate istream, ostream, and iomanip *)


Module ostream.
  Section with_cpp.
    Context `{Σ : cpp_logic, σ : genv}.

    (** Run the handler on each character in the string *)
    Fixpoint bs_dos (OS : Ostream) (bs : bs) (K : mpred) : mpred :=
      |={⊤}=>
      match bs with
      | BS.EmptyString => K
      | BS.String b bs => OS.(do) {[Write $ Byte.to_N b]} $ fun _ => bs_dos OS bs K
      end.
    #[global] Hint Opaque bs_dos : sl_opacity.
    Lemma bs_dos_fupd OS bs K : bs_dos OS bs K ⊣⊢ |={⊤}=> bs_dos OS bs K.
    Proof. by destruct bs => /=; rewrite fupd_idemp. Qed.

    #[global] Instance elim_modal_fupd_wp_lval E OS bs p P Q :
      ElimModal True p false (|={E}=> P) P (bs_dos OS bs Q) (bs_dos OS bs Q).
    Proof.
      rewrite /ElimModal. rewrite bi.intuitionistically_if_elim/=.
      rewrite {2}bs_dos_fupd. iIntros (?) "[>h k] !>"; iApply "k"; done.
    Qed.
    #[global] Instance elim_modal_bupd_wp_lval OS bs p P Q :
      ElimModal True p false (|==> P) P (bs_dos OS bs Q) (bs_dos OS bs Q).
    Proof.
      rewrite /ElimModal (bupd_fupd top). exact: elim_modal_fupd_wp_lval.
    Qed.
    #[global] Instance add_modal_fupd_wp_lval OS bs P Q : AddModal (|={top}=> P) P (bs_dos OS bs Q).
    Proof.
      rewrite/AddModal.
      rewrite {2}bs_dos_fupd. iIntros "[>h k] !>"; iApply "k"; done.
    Qed.

    #[global]
    Instance bs_dos_proper_frame (OS: Ostream) b
      : kont.ProperFrame (T:=[tele]) (bs_dos OS b).
    Proof.
      constructor; intros.
      induction b; simpl.
      { iIntros "X >K !>"; iRevert "K"; iApply ("X" $! ()). }
      { iIntros "X". destruct OS.
        iIntros ">Y !>"; iRevert "Y".
        iApply (do_frame {[Write $ Byte.to_N b]}).(kont._frame).
        iIntros ([?[]]); simpl.
        iApply IHb. iAssumption. }
    Qed.

    #[global]
    Instance bs_dos_positive_proper_frame_eta (OS: Ostream) b
      : kont.ProperFrame (T:=[tele]) (fun x => bs_dos OS b x).
    Proof. apply bs_dos_proper_frame. Qed.

    cpp.spec "std::operator<<<std::char_traits<char>>(std::basic_ostream<char, std::char_traits<char>>&, const char*)"
      from source as ostream_insert_spec with (
      \arg{osP} "" (Vptr osP)
      \prepost{OS γ} osP |-> ostream.R OS γ 1$m
      \arg{strP} "" (Vptr strP)
      \prepost{q__s strM} strP |-> cstring.R q__s strM
      \pre{Q} bs_dos OS strM Q
      \post[Vptr osP] Q).

    Parameter format_int : Z -> bs.
    #[global] Declare Instance format_int_inj : Inj eq eq format_int.
    (** TODO: find an implementation!*)

    cpp.spec "std::basic_ostream<char, std::char_traits<char>>::operator<<(int)"
      from source as ostream_print_int_spec with (
      \this this
      \arg{n} "" (Vint n)
      \prepost{OS γ} this |-> ostream.R OS γ 1$m
      \pre{Q} bs_dos OS (format_int n) Q
      \post[Vptr this] Q
    ).

    cpp.spec "std::basic_ostream<char, std::char_traits<char>>::operator<<(unsigned long)"
      from source as ostream_print_ulong_spec with (
      \this this
      \arg{n} "" (Vint n)
      \prepost{OS γ} this |-> ostream.R OS γ 1$m
      \pre{Q} bs_dos OS (format_int n) Q
      \post[Vptr this] Q
    ).

    Definition iostream_manip_spec contents_f : WpSpec_cpp_val := (
      \arg{osP : ptr} "" (Vptr osP)
      (* XXX: manipulators can cause output! *)
      \prepost{OS γ} osP |-> ostream.R OS γ 1$m
      \pre{Q} bs_dos OS contents_f Q
      \post[Vptr osP] Q).

    Definition ostream_cpp_type : type :=
      "std::basic_ostream<char, std::char_traits<char>>&".
    Definition iostream_manip_kind : okind :=
      tFunction ostream_cpp_type [ostream_cpp_type].

    cpp.spec "std::endl<char, std::char_traits<char>>(std::basic_ostream<char, std::char_traits<char>>&)"
      from source as endl_spec with (
      \exact Reduce iostream_manip_spec "
"%bs
    ).

    (* This is the overload taking the endl manipulator. *)
    (* https://eel.is/c++draft/output.streams#ostream.inserters *)
    cpp.spec "std::basic_ostream<char, std::char_traits<char>>::operator<<(std::basic_ostream<char, std::char_traits<char>>&(*)(std::basic_ostream<char, std::char_traits<char>>&))"
      from source as ostream_insert_string_spec with (
      \this this
      \arg{os_f} "" (Vptr os_f)
      \pre{spec} os_f |-> unmaterialized_specR iostream_manip_kind spec
      (* ^^ this would be *slightly* more general if it took a materialized specification *)
      \pre{Q} (spec [Vref this] (fun v => [| v = Vptr this |] ** Q))
      \post[Vptr this] Q
    ).


  End with_cpp.
End ostream.

Module istream.
  Section with_cpp.
    Context `{Σ : cpp_logic, σ : genv}.

    Variant input_char : Type -> Type :=
      | read : input_char N.

    Definition as_event (T : Type) (act : input_char T) : T -> input_event :=
      match act in input_char T return T -> _ with
      | read => fun n => Read n
      end.

    (** [is_ws] returns true if the character is a standard whitespace 
        (space, \n, \r, \t, \v, \f). *)
    Definition is_ws (c : N) : bool :=
      bool_decide (c = 32 \/ c = 10 \/ c = 13 \/ c = 9 \/ c = 11 \/ c = 12)%N.

    (** [as_digit] returns [Some d] if the character is between '0' and '9'.
        Uses stdpp's bool_decide to evaluate the logical conjunction. *)
    Definition as_digit (c : N) : option N :=
      if bool_decide (48 <= c /\ c <= 57)%N then
        Some (c - 48)%N
      else
        None.

    (** [read_int] reads characters using [Do read] and parses
        the string as an integer. For example, the characters
        <1>, <2>, <\n> would return <('\n', 12)>.

        The function accepts both positive and negative integers.

        The first component is the "overread", the first byte read that
        is not part of the number.
    *)
    CoFixpoint read_int : itree input_char (N * Z) :=
      (* Internal state machine to accumulate parsed digits *)
      let cofix loop (sign : Z) (acc : Z) : itree input_char (N * Z) :=
        Do read (fun c =>
          match as_digit c with
          | Some digit =>
            loop sign (acc * 10 + Z.of_N digit)%Z
          | None =>
            (* Not a digit: return the delimiter character and the final signed integer *)
            Ret (c, (sign * acc)%Z)
          end
        )
      in

      Do read (fun c =>
        if (c =? 45)%N then
          (* Encountered '-' (ASCII 45) -> Start reading negative number *)
          loop (-1)%Z 0%Z

        else if (c =? 43)%N then
          (* Encountered '+' (ASCII 43) -> Start reading positive number *)
          loop 1%Z 0%Z

        else if is_ws c then
          (* Whitespace -> Co-recursively skip *)
          read_int

        else match as_digit c with
            | Some digit =>
                (* Encountered a digit -> Start accumulating a positive number *)
                loop 1%Z (Z.of_N digit)
            | None =>
                (* Unexpected character before any digits -> Abort and return 0 *)
                Ret (c, 0%Z)
            end
        ).

    (** This contract only covers parsed values representable as [int].
        Out-of-range extraction saturates and sets [failbit], which the current
        stream predicate does not model.

        TODO: this specification is unsound because it needs to re-buffer the
        next character that it read (the first component of the pair returned by
        [read_int]).
     *)
    cpp.spec "std::basic_istream<char, std::char_traits<char>>::operator>>(int&)"
      from source as istream_take_int_spec with (
          \this this
          \pre{IS isM} this |-> istream.R IS isM 1$m
          \arg{nP} "" (Vref nP)
          \pre nP |-> anyR "int" 1$m
          \pre{K : Z -> mpred} interp_itree as_event IS read_int (fun '(_, n) =>
            [| (int_rank.min_val int_rank.Iint Signed <= n <=
                int_rank.max_val int_rank.Iint Signed)%Z |] ** K n)
          \post[Vptr this] Exists isM' n,
            this |-> istream.R IS isM' 1$m **
              nP |-> intR 1$m n **
              K n
        ).

  End with_cpp.

End istream.
