Require Import List.
Import ListNotations.

Require Import ZArith.
Require Import String.
Require Import Bool.

AddPath "/Users/joald/wwk/client" as.

Load packet.

Open Scope list_scope.

Inductive directive : Set :=
| SEND_PACKET
| WRITE_CONTENTS
| SEND_TO : positive -> directive
| PRINT.

Record state : Set := mkState {
  orders : list directive;
  transfer_mode : mode;
  port: option positive;
  last_packet : packet;
  last_block_id : N;
  did_retransmit : bool;
  finished : bool;
  file_contents : string;
}.


Record result := mkResult {
  (* the packet that the client needs to send next *)
  packet_to_send : string; 

  (* next state *)
  new_state : state;
}.

(** When reading:
  - in_file is the name of the file on the server.
  - out_file is the name of the file on the local machine.
    When writing:
  - in_file is the contents of the file on the local machine.
  - out_file is the name of the file on the server
*)
Definition coq_init (rw_mode : mode) (in_file : string) (out_file : string) : result := 
  let pac := init_packet rw_mode in_file out_file in
  mkResult
    (serialize_packet pac)
    (mkState ([SEND_PACKET]) rw_mode None pac 0 false false
      match rw_mode with
      | Read => ""
      | Write => in_file
      end).

Theorem init_when_reading_infile_is_in_packet : forall infil outfil, 
  let p := packet_to_send (coq_init Read infil outfil) in
  substring 2 (length infil) p = infil.
Proof.
intros.
magic.
elim infil.
* magics.
* magic.
  rewrite H.
  auto.
Qed.

Theorem init_when_reading_file_contents_is_empty : forall infil outfil,
  file_contents (new_state (coq_init Read infil outfil)) = EmptyString.
Proof. magic. Qed.

Theorem init_when_writing_out_file_is_in_packet : forall infil outfil, 
  let p := packet_to_send (coq_init Write infil outfil) in
  substring 2 (length outfil) p = outfil.
Proof.
intros.
magic.
elim outfil.
* magics.
* magic.
  rewrite H.
  auto.
Qed.

Theorem init_when_writing_file_contents_is_infile : forall infil outfil,
  file_contents (new_state (coq_init Write infil outfil)) = infil.
Proof. magic. Qed.

Definition illegal_operation (err_msg : string) (st : state) : result := mkResult
  (serialize_packet (p_ERROR ILLEGAL_TFTP_OPERATION err_msg))
  (mkState [SEND_PACKET] (transfer_mode st) (port st) (last_packet st) (last_block_id st) false true "").

Definition wrong_source_port (st : state) (p : positive) : result := mkResult 
  (serialize_packet (p_ERROR UNKNOWN_TRANSFER_ID ""))
  (mkState [SEND_TO p] (transfer_mode st) (port st) (last_packet st) (last_block_id st) (did_retransmit st) (finished st) (file_contents st)).

Definition request_retransmit (st : state) : result := 
  if did_retransmit st
    then mkResult "The server timed out."
      (mkState [PRINT] (transfer_mode st) (port st) (last_packet st) (last_block_id st) true true "")
    else mkResult 
      (serialize_packet (last_packet st))
      (mkState [SEND_PACKET] (transfer_mode st) (port st) (last_packet st) (last_block_id st) true (finished st) (file_contents st)).

Definition send_bytes (st : state) (byte_count : nat) : forall new_id, new_id < two_bytes_range_size -> result := fun new_id prop =>
  let to_send := substring 0 byte_count (file_contents st) in
  let rest    := substring byte_count (length (file_contents st) - byte_count) (file_contents st) in
  let pac     := p_DATA new_id prop to_send in
  mkResult
    (serialize_packet pac)
    (mkState [SEND_PACKET] Write (port st) pac new_id false (N_of_nat byte_count <? 512) rest).

Definition coq_process_packet (pack : string) (st : state) (p : positive) (timeout : bool) : result.
Proof.
Open Scope positive_scope.
refine (
  if finished st
    then mkResult "" st
    else _
).
refine (
  if timeout 
    then request_retransmit st 
    else _
).
refine (
  if (
    match port st with 
    | None => false 
    | Some p2 => negb (Pos.eqb p p2)
    end 
  ) then wrong_source_port st p
    else _
).
destruct (deserialize_packet pack).
+ destruct p0.
  - exact (illegal_operation "Cannot send read requests to client." st).
  - exact (illegal_operation "Cannot send write requests to client." st).
  - (* p_DATA *)
    remember x as nr.
    remember l as prop.
    remember s as data.

    refine (
      match transfer_mode st with
      | Read => _
      | Write => illegal_operation "Cannot receive data in write mode." st
      end
    ).
    Local Close Scope positive_scope.
    Local Open Scope N_scope.
    refine (
      if nr =? last_block_id st + 1
        then _
        else illegal_operation "Incorrect block number." st
    ).
    refine (
      if negb (N_of_nat (length data) =? 512)
        then mkResult "" (mkState [WRITE_CONTENTS] Read (port st) 
          (last_packet st) nr false true (file_contents st ++ data))
        else let pac := (p_ACK nr prop) in
          mkResult (serialize_packet pac)
            (mkState [SEND_PACKET] Read (Some p) pac nr 
                false false (file_contents st ++ data))
    ).
  - (* p_ACK *)
    remember x as nr.
    refine (
      match transfer_mode st with
      | Read => illegal_operation "Cannot receive data in write mode." st
      | Write => _
      end
    ).
    case_eq (two_bytes_range_size ?= nr + 1).
    * intro.
      assert (two_bytes_range_size = nr + 1).
      { apply (N.compare_eq_iff two_bytes_range_size (nr + 1)).
        assumption. }
      exact (illegal_operation "File too large." st).
    * intro.
      assert (two_bytes_range_size < nr + 1).
      { apply (N.compare_lt_iff two_bytes_range_size (nr + 1)).
        assumption. }
      exact (illegal_operation "File too large." st).
    * intro.
      assert (nr + 1 < two_bytes_range_size).
      { apply (N.compare_gt_iff two_bytes_range_size (nr + 1)).
        assumption. }
      remember (N_of_nat (length (file_contents st))) as CL.
      case_eq (CL ?= 512).
      -- intro.
         assert (CL = 512).
         { apply (N.compare_eq_iff CL 512).
           assumption. }
         exact (send_bytes st 512 (nr + 1) H0).
      -- intro.
         assert (CL < 512).
         { apply (N.compare_lt_iff CL 512).
           assumption. } 
         exact (send_bytes st (nat_of_N CL) (nr + 1) H0).
      -- intro.
         assert (512 < CL).
         { apply (N.compare_gt_iff CL 512).
           assumption. } 
         exact (send_bytes st 512 (nr + 1) H0).
  - (* p_ERROR *)
    remember s as err_msg.
    exact (
      mkResult err_msg
        (mkState [PRINT] (transfer_mode st) (port st) (last_packet st) (last_block_id st) false true (file_contents st))
    ).

+ exact (illegal_operation "Cannot understand package." st).
Defined.

(*
Inductive packet : Set := 
| p_RRQ : string -> packet                  (* Filename *)
| p_WRQ : string -> packet                  (* Filename *)
| p_DATA : forall (x : N), x < two_bytes_range_size -> string -> packet     (* Block #, Data *)
| p_ACK : forall (x : N), x < two_bytes_range_size -> packet                (* Block # *)
| p_ERROR : error_code -> string -> packet. (* ErrorCode, ErrMsg *)

Record state : Set := mkState {
  orders : list directive;
  transfer_mode : mode;
  port: option positive;
  last_packet : packet;
  did_retransmit : bool;
  finished : bool;
  file_contents : string;
}.
Record result := mkResult {
  (* the packet that the client needs to send next *)
  packet_to_send : string; 

  (* next state *)
  new_state : state;
}.
*)