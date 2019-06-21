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

Local Close Scope positive_scope.
Local Open Scope nat_scope.

Lemma string_length_cons : forall s c, S(length s) = length (String c s).
Proof. magics. Qed.

Definition elem_str (s : string) (c : ascii) := exists n, get n s = Some c.

Theorem empty_string_is_empty : forall c, ~elem_str EmptyString c.
Proof. 
magics.
unfold elem_str in H.
unfold get in H.
destruct H.
magics.
Qed.

Theorem remove_last_no_remove_first : forall s c1 c2, 
  remove_last (String c1 (String c2 s)) = String c1 (remove_last (String c2 s)).
Proof. magics. Qed.

Local Open Scope string_scope.

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
