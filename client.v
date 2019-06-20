Require Import ZArith.
Require Import String.

AddPath "/Users/joald/wwk/client" as.

Load packet.

Record state : Set := mkState {
  transfer_mode : mode;
  port: option positive;
  last_packet : option packet;
  timeout_count : N;
  file_contents : string;
}.

(*
Inductive packet : Set := 
| p_RRQ : string -> packet                  (* Filename *)
| p_WRQ : string -> packet                  (* Filename *)
| p_DATA : forall (x : N), x < two_bytes_range_size -> string -> packet     (* Block #, Data *)
| p_ACK : forall (x : N), x < two_bytes_range_size -> packet                (* Block # *)
| p_ERROR : error_code -> string -> packet. (* ErrorCode, ErrMsg *)
*)

Record result := mkResult {
  packet_to_send : option packet;
  new_state : option state;
  file_data : option string;
}.

(** When reading:
  - in_file is the name of the file on the server.
  - out_file is the name of the file on the local machine.
  When writing:
  - in_file is the contents of the file on the local machine.
  - out_file is the name of the file on the server
*)
Definition coq_init (rw_mode : mode) (in_file : string) (out_file : string) : result := 
  (serialize_packet (init_packet mode in_file out_file), 
   mkState mode None None (?) match

Definition coq_process_state () := .
