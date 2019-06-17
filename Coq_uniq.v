Require Import ZArith.
Require Import Ascii.
Require Import List.
Require String.

Import ListNotations.

Local Open Scope char_scope.

Axiom newline : ascii.

Record uniq_state_info := mkgst {
    cur_line : String.string;
    prev_line : String.string;
    line_number : Z;
}.

Inductive uniq_state :=
| Reading_line (s : uniq_state_info)
| Line_uniq (s : uniq_state_info)
| End_of_line (s: uniq_state_info)
| End_of_file (s: uniq_state_info)
| Done
| Error.

Definition initial_state :=
  Reading_line {| cur_line := String.EmptyString;
                  prev_line := String.EmptyString;
                  line_number := 0%Z;
               |}.

Inductive uniq_action :=
| Print_line (line_number : Z) (line : String.string)
| Input_char
| Continue
| Quit
| RaiseError.

Inductive uniq_input :=
| Char (c : ascii)
| No_input.

Definition get_line_number (s : uniq_state) : Z :=
  match s with
  | Reading_line si => si.(line_number)
  | Line_uniq si => si.(line_number)
  | End_of_line si => si.(line_number)
  | End_of_file si => si.(line_number)
  | Done => -1
  | Error => -1
  end.

Definition string_of_char (c : ascii) :=
  (String.String c String.EmptyString).

Definition line_match (si : uniq_state_info) :=
  String.string_dec si.(prev_line) si.(cur_line).

Definition next_line (si : uniq_state_info) :=
  {| cur_line := String.EmptyString;
     prev_line := si.(cur_line);
     line_number := si.(line_number) + 1;
  |}.

Definition next_char (si : uniq_state_info) (c : ascii) :=
  {| cur_line := String.append si.(cur_line) (string_of_char c);
     prev_line := si.(prev_line);
     line_number := si.(line_number);
  |}.

Definition do_uniq (s : uniq_state) (i : uniq_input) : (uniq_action * uniq_state) :=
  match s, i with
  | Reading_line si, Char c =>
    if ascii_dec c newline then
      (Continue, End_of_line (next_char si c))
    else
      (Input_char, Reading_line (next_char si c))
  | Reading_line si, No_input =>
     (Continue, End_of_file si)

  | End_of_line si, No_input =>
    if line_match si then
      (Input_char, Reading_line (next_line si))
    else
      (Print_line si.(line_number) si.(cur_line), Line_uniq si)
  | Line_uniq si, _ => (Input_char, Reading_line (next_line si))
  | End_of_file si, _ =>
    if line_match si then
      (Quit, Done)
    else
      (Print_line si.(line_number) si.(cur_line), Done)
  | Done, _ => (Quit, Done)
  | _, _ => (RaiseError, Error)
  end.

Inductive line : String.string -> Prop :=
| line_empty : line (string_of_char newline)
| line_cons : forall c l', line l' -> c <> newline -> line (String.String c l').

Inductive run : uniq_action -> uniq_state -> String.string -> list String.string -> Prop :=
| run_cons : forall a s s' cl n l out,
    do_uniq s No_input = (a, s') ->
    run a s' cl out -> run (Print_line n l) s cl (l :: out)
| run_inp : forall a s s' c cl out,
    do_uniq s (Char c) = (a, s') ->
    run a s' cl out -> run Input_char s (String.String c cl) out
| run_eof : forall a s s' out,
    do_uniq s No_input = (a, s') ->
    run Input_char s (String.EmptyString) out
| run_quit : forall s cl out,
    run Quit s cl out
| run_continue : forall a s s' cl out,
    do_uniq s No_input = (a, s') ->
    run a s' cl out ->
    run Continue s cl out.

(* Theorem run_duplicated : *)
(*   forall l, line l -> run Input_char (initial_state) (String.append l l) [l]. *)
(* Proof. *)
(*   intros. *)
(*   induction H. *)
(*   * eapply run_inp; simpl. *)
(*     destruct (ascii_dec newline newline); eauto; congruence. *)
(*     eapply run_continue; compute; eauto. *)
(*     eapply run_cons. compute; eauto. *)
(*     eapply run_inp; simpl. *)
(*     destruct (ascii_dec newline newline); eauto; congruence. *)
(*     eapply run_continue; simpl. *)
(*     unfold next_char, string_of_char; simpl. unfold line_match. destruct (String.string_dec *)
(*       (prev_line *)
(*          {| *)
(*          cur_line := String.String newline String.EmptyString; *)
(*          prev_line := String.String newline String.EmptyString; *)
(*          line_number := 1 |}) *)
(*       (cur_line *)
(*          {| *)
(*          cur_line := String.String newline String.EmptyString; *)
(*          prev_line := String.String newline String.EmptyString; *)
(*          line_number := 1 |})). eauto. simpl in *. congruence. *)
(*     eapply run_eof; compute; eauto. *)
(*   * eapply run_inp; simpl. *)
(*     destruct (ascii_dec c newline). eauto; congruence. *)

(* Admitted. *)
