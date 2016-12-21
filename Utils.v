
Definition remove_option {T T' : Type} (f : T -> option T') x (P: f x <> None) : T' :=
  match f x as res return (res <> None -> T') with
    | Some t => fun _ => t
    | None => fun P0 => False_rect _ (P0 eq_refl)
  end P.

Lemma remove_option_sound : forall (T T' : Type) (f: T -> option T') x P,
  f x = Some (remove_option f x P).
Proof.
  intros.
  unfold remove_option.
  destruct (f x).
  + reflexivity.
  + contradiction.
Qed.

(*

Definition swap_new {T : Type} (n : nat) (ws : list T) (E : 1+n < length ws) :=
  remove_option (swap n) ws (swap_long' T n ws E).

Definition option_mkstack (st : list word) : option stack_t :=
  match le_lt_dec BOUND (length st) with
    | right LEN => Some (mkstack st LEN)
    | left _ => None
  end.
*)