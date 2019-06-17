Require Import ZArith.


Local Open Scope positive_scope.

Unset Elimination Schemes.
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


Lemma nr_opcode_ident : forall x, (x = 1 \/ x = 2 \/ x = 3 \/ x = 4 \/ x = 5) ->
  match nr_to_opcode x with 
    | Some opcode => x = opcode_to_nr opcode
    | None => True
  end.
Proof.
intros x bounds.
case bounds.
* intros.
  rewrite H.
  unfold nr_to_opcode.
  auto.
* intros bounds2.
  case bounds2.
  + intros.
    rewrite H.
    unfold nr_to_opcode.
    auto.
  + intros bounds3.
    case bounds3.
    - intros.
      rewrite H.
      unfold nr_to_opcode.
      auto.
    - intros bounds4.
      case bounds4.
      all: intros.
      all: rewrite H.
      all: unfold nr_to_opcode.
      all: auto.
Qed.


Lemma nr_opcode_none : forall x, x > 5 \/ x < 1 -> nr_to_opcode x = None.
Proof.
intros.
unfold nr_to_opcode.
case H.
* intro gt5.
  destruct x.
  + destruct x.
    - trivial.
    - destruct x; easy.
    - easy.
  + destruct x.
    - trivial.
    - destruct x; easy.
    - easy.
  + easy.
* intro.
  destruct x.  
  all: easy.
Qed.

Require Import Ascii.

Open Scope char_scope.

Definition opcode_to_ascii (op : packet_opcode) : ascii :=
   ascii_of_pos (opcode_to_nr op).

Theorem opcode_to_ascii_and_back : forall op : packet_opcode, N_of_ascii (opcode_to_ascii op) = Npos (opcode_to_nr op).
Proof.
intros.
destruct op.
all: simpl.
all: trivial.
Qed.

(* FMLLLLL
      all: auto.
      exfalso.
      assert (5 < 4).
      { apply Pos.gt_lt_iff. assumption. }
      assert (2 < 1).
      { apply Pos.succ_lt_mono. apply Pos.succ_lt_mono. apply Pos.succ_lt_mono. assumption. }
      apply (Pos.nlt_1_r 2).
      assumption.
    - exfalso.
      easy.
      assert (5 < 2).
      { apply Pos.gt_lt_iff. assumption. }
      assert (4 < 1).
      { apply Pos.succ_lt_mono. assumption. }
      apply (Pos.nlt_1_r 4).
      assumption.
  + exfalso.
    cut (5 < 1).
    ** intros.
       apply (Pos.nlt_1_r 5).
       assumption.
    ** apply Pos.gt_lt_iff. assumption.
* intros lt1.
  exfalso.
  apply (Pos.nlt_1_r x).
  assumption.
Qed.*)

Inductive error_code : Set := 
| NOT_DEFINED 
| FILE_NOT_FOUND 
| ACCESS_VIOLATION
| DISK_FULL_OR_ALLOCATION_EXCEEDED
| ILLEGAL_TFTP_OPERATION
| UNKNOWN_TRANSFER_ID
| FILE_ALREADY_EXISTS.



Inductive mode : Set := Read | Write.


Require Import String.

Inductive packet : Set := 
| p_RRQ : string -> packet                  (* Filename *)
| p_WRQ : string -> packet                  (* Filename *)
| p_DATA : positive -> string -> packet     (* Block #, Data *)
| p_ACK : positive -> packet                (* Block # *)
| p_ERROR : error_code -> string -> packet. (* ErrorCode, ErrMsg *)


Definition init_packet (m : mode) (filename : string) : packet := 
  match m with
  | Read => p_RRQ filename
  | Write => p_WRQ filename
  end.

Theorem init_packet_read_rrq : forall s : string, forall m : mode, m = Read -> init_packet m s = p_RRQ s.
Proof.
intros.
unfold init_packet.
rewrite H.
auto.
Qed.

Theorem init_packet_write_wrq : forall s : string, forall m : mode, m = Write -> init_packet m s = p_WRQ s.
Proof.
intros.
unfold init_packet.
rewrite H.
auto.
Qed.




Definition serialize_packet (p : packet) : string := 
  match p with
  | p_RRQ filename => String "000" (String (opcode_to_ascii RRQ) (filename ++ String "000" ("octet" ++ String "000" EmptyString))).
  | p_WRQ filename => String "000" (String (opcode_to_ascii WRQ) (filename ++ String "000" ("octet" ++ String "000" EmptyString))).
  | p_DATA 

(* client *)



Record init_state : Set := mkState {
    transfer_mode : mode;
    filename : string;
    port: positive;
    last_packet : option packet;
    timeout_count : N;
}.

Definition coq_process_state () := .
