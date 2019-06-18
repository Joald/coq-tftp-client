Require Import String ZArith Ascii.

(* Opcodes. *)

Local Open Scope positive_scope.

Inductive packet_opcode : Set := RRQ | WRQ | DATA | ACK | ERROR.

Definition opcode_to_nr (code: packet_opcode) :=
  match code with  
  | RRQ   => 1
  | WRQ   => 2
  | DATA  => 3
  | ACK   => 4
  | ERROR => 5
  end.

Lemma opcode_range : forall x, 1 <= opcode_to_nr x <= 5.
Proof.
intros.
destruct x.
all: easy.
Qed.


Definition nr_to_opcode (nr: positive) : option packet_opcode := 
  match nr with
  | 1 => Some RRQ
  | 2 => Some WRQ
  | 3 => Some DATA
  | 4 => Some ACK
  | 5 => Some ERROR
  | _ => None
  end.

Lemma nr_opcode_ident : forall x, x <= 5 ->
  match nr_to_opcode x with 
    | Some opcode => x = opcode_to_nr opcode
    | None => True
  end.
Proof.
intros x bound.
unfold opcode_to_nr.
destruct x; simpl.
* destruct x; auto.
  destruct x; auto.
* destruct x; auto.
  destruct x; auto.
* auto.
Qed.




Lemma nr_opcode_none : forall x, x > 5 \/ x < 1 -> nr_to_opcode x = None.
Proof.
intros.
unfold nr_to_opcode.
case H.
* intro gt5.
  destruct x.
  + destruct x; auto.
    - destruct x; easy.
    - easy.
  + destruct x; auto.
    - destruct x; easy.
    - easy.
  + easy.
* intro.
  destruct x.
  all: easy.
Qed.


Definition opcode_to_ascii (op : packet_opcode) : ascii :=
   ascii_of_pos (opcode_to_nr op).

Definition ascii_to_opcode (c : ascii) : option packet_opcode :=
  match N_of_ascii c with
  | Npos p => nr_to_opcode p
  | _ => None
  end.

Theorem opcode_ascii_ident : 
  forall op : packet_opcode, 
  Some op = ascii_to_opcode (opcode_to_ascii op).
Proof.
intros.
destruct op; auto.
Qed.

Definition opcode_to_string (op : packet_opcode) : string := 
  String zero (String (opcode_to_ascii op) EmptyString).
