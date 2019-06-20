Require Import ZArith String Ascii NZAxioms.

(* Auxiliary. *)

Ltac magic := intros; auto; try easy; try intuition; simpl.

Ltac black_magic := intros; auto; try easy; try intuition; try zify; try omega; simpl.

Ltac magics := repeat black_magic.

Local Open Scope N_scope.

Definition byte_range_size := 256.

Definition two_bytes_range_size := 65536.

Definition ascii_to_string (c : ascii) : string := String c EmptyString.

Definition two_ascii_to_string (c1 : ascii) (c2 : ascii) : string :=
  String c1 (String c2 EmptyString).

(* Convert a number in the range 0 <= n < 65536 to a two-char string. *)
Definition word_no_to_string (word_no : N) : string := two_ascii_to_string 
  (ascii_of_N (word_no / byte_range_size)) 
  (ascii_of_N (word_no mod byte_range_size)).

(* Convert a number in the range 0 <= n < 65536 encoded in a two-char string to N. *)
Definition string_to_word_no (s: string) : option N :=
  match s with
  | String c1 (String c2 EmptyString) => Some (N_of_ascii c1 * byte_range_size + N_of_ascii c2)
  | _ => None
  end.

Lemma char_less_than_256 : forall c, N_of_ascii c < byte_range_size.
Proof.
intros.
destruct c.
destruct b;
destruct b0;
destruct b1;
destruct b2;
destruct b3;
destruct b4;
destruct b5;
destruct b6;
easy.
Qed.

Theorem string_to_word_no_in_range : forall s x, 
  string_to_word_no s = Some x -> x < two_bytes_range_size.
Proof.
unfold string_to_word_no.
simpl.
intros s x.
destruct s; auto.
* intros.
  exfalso.
  inversion H.
* destruct s; auto.
  + intros.
    exfalso.
    inversion H.
  + destruct s; auto.
    2: intro.
    2: exfalso.
    2: inversion H.
assert (N_of_ascii a < byte_range_size) as aLower.
{ apply (char_less_than_256 a). }

assert (N_of_ascii a0 < byte_range_size) as a0Lower.
{ apply (char_less_than_256 a0). }
intro.
assert (N_of_ascii a * byte_range_size + N_of_ascii a0 = x) as Rew.
{ inversion H. 
  auto. }
rewrite <- Rew.
clear Rew.
clear H.
clear x.
destruct (N_of_ascii a); destruct (N_of_ascii a0); auto.
- assert (0 * byte_range_size + N.pos p = N.pos p).
  { easy. }
  rewrite H.
  assert (byte_range_size < two_bytes_range_size).
  { easy. }
  rewrite a0Lower.
  assumption.
- rewrite (N.add_0_r (N.pos p * byte_range_size)).
  assert (byte_range_size * byte_range_size = two_bytes_range_size).
  { easy. }
  rewrite <- H.
  rewrite <- (N.mul_lt_mono_pos_r byte_range_size (N.pos p) byte_range_size).
  -- assumption.
  -- easy.
- assert (N.pos p * byte_range_size <= (byte_range_size - 1) * byte_range_size).
  { magics. }
  magic. 
  unfold two_bytes_range_size.
  Local Close Scope N_scope.
  Local Open Scope positive_scope.
  cut (p * 256 + p0 < 65536).
  { magics. }
  unfold byte_range_size in H.
  unfold byte_range_size in aLower.
  unfold byte_range_size in a0Lower.
  simpl in H.
  magics.
Qed.


Local Close Scope positive_scope.
Local Open Scope N_scope.

Lemma div_mul_mod_ident : forall x y, y <> 0 -> x / y * y + x mod y = x.
Proof.
intros.
rewrite (N.mul_comm (x / y) y).
rewrite <- (N.div_mod x y).
all: auto.
Qed.

Theorem word_no_string_ident : forall word_no, 
  word_no < two_bytes_range_size -> 
  Some word_no = string_to_word_no (word_no_to_string word_no).
Proof.
intros.
simpl.

assert (word_no < byte_range_size * byte_range_size).
{ easy. }

assert (word_no / byte_range_size < byte_range_size) as UpperIneq.
{ apply N.div_lt_upper_bound; auto.
  easy. }

assert (word_no mod byte_range_size < byte_range_size) as LowerIneq.
{ apply N.mod_bound_pos.
  * destruct word_no; easy.
  * easy. }

rewrite (N_ascii_embedding (word_no / byte_range_size)).
* rewrite (N_ascii_embedding (word_no mod byte_range_size)).
  + rewrite (div_mul_mod_ident word_no byte_range_size).
    - auto.
    - easy.
  + easy.
* easy.
Qed.


Local Close Scope N_scope.
Local Open Scope positive_scope.

(*Definition null_terminate (s : string) : string :=
  s ++ String zero EmptyString.
*)

Fixpoint null_terminate (s : string) : string :=
  match s with
  | EmptyString => String zero EmptyString
  | String c rest => String c (null_terminate rest)
  end.

Fixpoint str_last (s : string) : ascii :=
  match s with
  | EmptyString => zero
  | String c EmptyString => c
  | String _ rest => str_last rest
  end.

Theorem last_null : forall s, str_last (null_terminate s) = zero.
Proof with magics.
magics.
unfold null_terminate...
unfold str_last...
elim s...
destruct s0...
Qed.

Fixpoint remove_last (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c EmptyString => EmptyString
  | String c rest => String c (remove_last rest)
  end.
(*
Fixpoint elem_str (s : string) (c : ascii) := 
  match s with
  | EmptyString => False
  | String c2 rest => c2 = c \/ (c2 <> c /\ elem_str rest c)
  end.
*)
Local Close Scope positive_scope.
Local Open Scope nat_scope.

Lemma string_length_cons : forall s c, S(length s) = length (String c s).
Proof. magics. Qed.

Definition elem_str (s : string) (c : ascii) := exists n, get n s = Some c.
(*
Lemma elem_str_in_str : forall s c, elem_str s c -> exists n, n < length s.
Proof.
magics.
unfold elem_str in H.
destruct H as [n G].
exists n.
destruct s.
* simpl in G.
  magics.
* simpl in G.
  destruct n.
  + magics.
  + unfold get in G. magic.
    rewrite <- (string_length_cons s a) in H.
    remember (length s) as l.
    rewrite 
    unfold length in H.
Qed.*)

Theorem empty_string_is_empty : forall c, ~elem_str EmptyString c.
Proof. 
magics.
unfold elem_str in H.
unfold get in H.
destruct H.
magics.
Qed.
(*
Theorem append_preserves_elems : forall s1 s2 c, (elem_str s1 c \/ elem_str s2 c) -> elem_str (s1 ++ s2) c.
Proof with magics.
magic.
* unfold elem_str.
  unfold elem_str in H0.
  destruct H0 as [x G].
  exists x.
  rewrite <- (append_correct1 s1 s2 x).
  + magic.
  + unfold get in G.
*)
Theorem remove_last_no_remove_first : forall s c1 c2, 
  remove_last (String c1 (String c2 s)) = String c1 (remove_last (String c2 s)).
Proof. magics. Qed.

Local Open Scope string_scope.
(*
Theorem remove_last_no_remove_concat : forall s1 s2 c, 
  remove_last (s1 ++ String c s2) = s1 ++ remove_last (String c s2).
Proof with magic.
intros.
elim s2.
* magics.
  elim s1.
  + magic.
  + intros.
    destruct s.
    - magics.
    - assert (String a (String a0 s) ++ String c EmptyString = String a (String a0 (s ++ String c EmptyString))).
      { magics. }
      rewrite H0.
      rewrite (remove_last_no_remove_first (s ++ String c "") a a0). 
      simpl (String a0 s ++ "") in H.
      simpl (String a (String a0 s) ++ ""). 
      rewrite <- H.
      magics.
* intros.
  assert (forall c s, remove_last (String c s) = String c (remove_last s) \/ remove_last (String c s) = EmptyString).
  { destruct s0.
    * right.
      magics.
    * left. apply (remove_last_no_remove_first s0 c0 a0). }
  rewrite (remove_last_no_remove_first s c a).
  destruct (H0 a s) as [|].
  + rewrite H1 in H.

  pattern (remove_last (String c s)) in H.
  simpl in HeqRcs.

  fold (match s with
         | "" => ""
         | String _ _ => String c (remove_last s)
         end) in HeqRcs.
Theorem remove_last_removes : forall s c, remove_last (s ++ (String c EmptyString)) = s.
Proof with magics.
magic.
elim s.
* magic.
* magic.
  rewrite H.
  remember ((s0 ++ String c EmptyString)%string) as s2.
  assert (s2 <> EmptyString).
  { (*remember (empty_string_is_empty c) as E.
    assert (elem_str s2 c).
    { remember (get (length s0) s2) as c2.
      unfold get in Heqc2. rewrite Heqs2 in Heqc2.
      
      +*) admit. }
  Search (_ ++ _)%string.
  unfold (neq) in H0.
  unfold remove_last in H.
*)
Theorem null_determination : forall s, remove_last (null_terminate s) = s.
Proof with magics.
magics.
induction s.
* magic.
* magics.
  assert (forall s, null_terminate s <> EmptyString).
  { intro.
    elim s0... }
  remember (H s) as NonE.
  rewrite IHs.
  assert (exists a b, null_terminate s = String a b).
  { destruct s.
    + simpl (null_terminate "").
      exists zero.
      exists ""...
    + exists a0.
      simpl.
      exists (null_terminate s)... }
  destruct H0.
  destruct H0.
  rewrite H0...
Qed.
