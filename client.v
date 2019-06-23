Require Import List.
Import ListNotations.

Require Import ZArith.
Require Import String.
Require Import Bool.

Require Import Coq.NArith.Nnat.


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

Definition change_orders (ords : list directive) (st : state) : state :=
  mkState ords (transfer_mode st) (port st) (last_packet st) (last_block_id st) (did_retransmit st) (finished st) (file_contents st).

Definition change_last_packet (lp : packet) (st : state) : state :=
  mkState (orders st) (transfer_mode st) (port st) lp (last_block_id st) (did_retransmit st) (finished st) (file_contents st).

Definition change_last_block_id (bid : N) (st : state) : state :=
  mkState (orders st) (transfer_mode st) (port st) (last_packet st) bid (did_retransmit st) (finished st) (file_contents st).

Definition change_did_retransmit (dr : bool) (st : state) : state :=
  mkState (orders st) (transfer_mode st) (port st) (last_packet st) (last_block_id st) dr (finished st) (file_contents st).

Definition change_finished (fin : bool) (st : state) : state :=
  mkState (orders st) (transfer_mode st) (port st) (last_packet st) (last_block_id st) (did_retransmit st) fin (file_contents st).

Definition change_file_contents (filc : string) (st : state) : state :=
  mkState (orders st) (transfer_mode st) (port st) (last_packet st) (last_block_id st) (did_retransmit st) (finished st) filc.

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

Require Import Coq.Program.Basics.
Open Scope program_scope.
Definition request_retransmit (st : state) : result := 
  if did_retransmit st
    then mkResult "The server timed out." 
      ((change_orders [PRINT] \u2218 change_did_retransmit true \u2218 change_finished true \u2218 change_file_contents "") st)
    else mkResult 
      (serialize_packet (last_packet st))
      (mkState [SEND_PACKET] (transfer_mode st) (port st) (last_packet st) (last_block_id st) true (finished st) (file_contents st)).

Definition send_bytes (st : state) (byte_count : nat) (new_id : N) : result :=
  let to_send := substring 0 byte_count (file_contents st) in
  let rest    := substring byte_count (length (file_contents st) - byte_count) (file_contents st) in
  let pac     := p_DATA new_id to_send in
  mkResult
    (serialize_packet pac)
    (mkState [SEND_PACKET] Write (port st) pac new_id false (N_of_nat byte_count <? 512) rest).

Definition port_is_bad (st : state) (p : positive) : bool :=
  match port st with 
  | None => false 
  | Some p2 => negb (Pos.eqb p p2)
  end.

Definition coq_process_packet (pack : string) (st : state) (p : positive) (timeout : bool) : result.
Proof.
Open Scope positive_scope.
refine (
  if finished st
    then mkResult "" (change_orders [] st)
    else _
).
refine (
  if timeout 
    then request_retransmit st 
    else _
).
refine (
  if port_is_bad st p
    then wrong_source_port st p
    else _
).
destruct (deserialize_packet pack).
+ destruct p0.
  - exact (illegal_operation "Cannot send read requests to client." st).
  - exact (illegal_operation "Cannot send write requests to client." st).
  - (* p_DATA *)
    remember n as nr.
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
        else let pac := (p_ACK nr) in
          mkResult (serialize_packet pac)
            (mkState [SEND_PACKET] Read (port st) pac nr 
                false false (file_contents st ++ data))
    ).
  - (* p_ACK *)
    remember n as nr.
    refine (
      match transfer_mode st with
      | Read => illegal_operation "Cannot receive data in write mode." st
      | Write => _
      end
    ).
    refine (
      if nr =? last_block_id st + 1
        then _
        else illegal_operation "Incorrect block number." st
    ).
    destruct (two_bytes_range_size ?= nr + 1).
    * exact (illegal_operation "File too large." st).
    * exact (illegal_operation "File too large." st).
    * remember (N_of_nat (length (file_contents st))) as CL.
      destruct (CL ?= 512).
      -- exact (send_bytes st 512 (nr + 1)).
      -- exact (send_bytes st (nat_of_N CL) (nr + 1)).
      -- exact (send_bytes st 512 (nr + 1)).
  - (* p_ERROR *)
    remember s as err_msg.
    exact (
      mkResult err_msg
        (mkState [PRINT] (transfer_mode st) (port st) (last_packet st) (last_block_id st) false true (file_contents st))
    ).

+ exact (illegal_operation "Cannot understand package." st).
Defined.

Theorem no_change_after_finish : forall pac st p timeout, 
  finished st = true -> finished (new_state (coq_process_packet pac st p timeout)) = true.
Proof with magics.
magics.
unfold coq_process_packet...
rewrite H...
Qed.

Theorem no_action_after_finish : forall pac st p timeout, 
  finished st = true -> orders (new_state (coq_process_packet pac st p timeout)) = [].
Proof with magics.
magics.
unfold coq_process_packet...
rewrite H...
Qed.

Definition normal_circumstances (st : state) (p : positive) (timeout : bool) : Prop :=
  finished st = false /\
  port_is_bad st p = false /\
  timeout = false.


Theorem finish_after_small_read : forall pac st p timeout num data,
  normal_circumstances st p timeout -> 
  transfer_mode st = Read -> 
  deserialize_packet pac = Some (p_DATA num data) ->
  num =? last_block_id st + 1 = true ->
  N_of_nat (length data) < 512 ->
  finished (new_state (coq_process_packet pac st p timeout)) = true.
Proof with magic.
intros pac st p timeout num data.
intros Normal ReadMode PacketData BlockIDOK PacketSmall.
unfold coq_process_packet...
unfold normal_circumstances in Normal.
destruct Normal as [FinF PortOK].
destruct PortOK as [PortOK TimeoutF].
rewrite FinF...
rewrite TimeoutF...
rewrite PortOK...
rewrite PacketData...
rewrite ReadMode... 
rewrite BlockIDOK...
assert (negb (N.of_nat (length data) =? 512) = true) as PacketIndeedSmall.
{ unfold negb.
  cut (N.of_nat (length data) =? 512 = false).
  { magics. rewrite H... }
  Search (_ =? _).
  apply (N.eqb_neq (N.of_nat (length data)) 512 ).
  magics.
}
rewrite PacketIndeedSmall.
magic.
Qed.

Theorem finish_after_small_write : forall pac st p timeout num,
  normal_circumstances st p timeout -> 
  transfer_mode st = Write -> 
  deserialize_packet pac = Some (p_ACK num) ->
  num = last_block_id st + 1 ->
  N_of_nat (length (file_contents st)) < 512 ->
  finished (new_state (coq_process_packet pac st p timeout)) = true.
Proof with magic.
intros pac st p timeout num.
intros Normal WriteMode PacketACK BlockIDOK PacketSmall.
unfold coq_process_packet.
unfold normal_circumstances in Normal.
destruct Normal as [FinF [PortOK TimeoutF]].
rewrite FinF...
rewrite TimeoutF...
rewrite PortOK...
rewrite PacketACK...
rewrite WriteMode...
rewrite BlockIDOK...
assert (N_of_nat (length (file_contents st)) ?= 512 = Lt) as NL.
{ apply (N.compare_lt_iff (N_of_nat (length (file_contents st))) 512).
  assumption. }
rewrite NL.
destruct (last_block_id st + 1 + 1).
* magics.
  rewrite (nat_of_N_of_nat (length (file_contents st))).
  rewrite (N.eqb_refl _).
  magic.
  rewrite (N.ltb_compare (N.of_nat (length (file_contents st))) 512).
  rewrite NL.
  magic.
* magics. 
  destruct ((65536 ?= p0)%positive).
  + rewrite (N.eqb_refl _).
    magics.
  + rewrite (N.eqb_refl _).
    magics.
  + rewrite (N.eqb_refl _).
    magics.
    rewrite (nat_of_N_of_nat (length (file_contents st))).
    rewrite (N.ltb_compare (N.of_nat (length (file_contents st))) 512).
    rewrite NL.
    magic.
Qed.

Theorem port_stays_the_same : forall pac st p timeout old_port,
  port st = Some old_port ->
  port (new_state (coq_process_packet pac st p timeout)) = Some old_port.
Proof with magic.
intros pac st p timeout old_port.
intros PortWasSet.
unfold coq_process_packet.
destruct (finished st).
{ magics. }
destruct timeout.
{ magics. 
  unfold request_retransmit.
  destruct (did_retransmit st).
  + magics.
  + magics. }
destruct (port_is_bad st p).
{ magics. }
destruct (deserialize_packet pac)...
destruct p0; magics;
destruct (transfer_mode st); magics;
destruct (n =? last_block_id st + 1)...
* destruct (negb (N.of_nat (length s) =? 512))...
* destruct (n + 1)...
  -- destruct (N.of_nat (length (file_contents st)) ?= 512)...
  -- destruct (65536 ?= p0)%positive...
     destruct (N.of_nat (length (file_contents st)) ?= 512)...
Qed.

Theorem bad_data_block_id_errors : forall pac st p p2 timeout num data,
  normal_circumstances st p timeout -> 
  transfer_mode st = Read -> 
  deserialize_packet pac = Some (p_DATA num data) ->
  num <> last_block_id st + 1 ->
  let res := coq_process_packet pac st p timeout in
    deserialize_packet (packet_to_send res) = Some p2 ->
      match p2 with (p_ERROR _ _) => True | _ => False end
    /\ finished (new_state res) = true.
Proof with magic.
intros pac st p p2 timeout num data.
intros Normals ReadMode GotData BadBlockID res.
unfold res.
clear res.
unfold coq_process_packet.
destruct Normals as [NotFin [PortOK NoTimeout]].
rewrite NotFin.
rewrite NoTimeout.
rewrite PortOK.
rewrite GotData.
rewrite ReadMode.
assert (num =? last_block_id st + 1 = false) as NEQ.
{ rewrite (N.eqb_compare num (last_block_id st + 1)).
  case_eq (num ?= last_block_id st + 1).
  - intro.
    exfalso.
    apply BadBlockID.
    apply (N.compare_eq_iff num (last_block_id st + 1)).
    assumption.
  - magic.
  - magic. }
rewrite NEQ.
magic.
simpl in H.
inversion H.
auto.
Qed.

Theorem correctly_acking_correct_nonfinal_packets : forall pac st p p2 timeout num data,
  normal_circumstances st p timeout -> 
  transfer_mode st = Read ->
  deserialize_packet pac = Some (p_DATA num data) ->
  num = last_block_id st + 1 ->
  N_of_nat (length data) = 512 -> 
  let res := coq_process_packet pac st p timeout in
     In SEND_PACKET (orders (new_state res))
  /\ (deserialize_packet (packet_to_send res) = Some p2 ->
  match p2 with
  | p_ACK ack_nr => ack_nr = num
  | _ => False
  end).
Proof with magic.
intros pac st p p2 timeout num data.
intros Normals ReadMode GotData GoodBlockID NonFinalPacket res.
unfold res.
unfold coq_process_packet.
destruct Normals as [NotFin [PortOK NoTimeout]].
rewrite NotFin.
rewrite NoTimeout.
rewrite PortOK.
rewrite GotData.
rewrite ReadMode.
rewrite NonFinalPacket.
assert (num =? last_block_id st + 1 = true) as NumEq.
{ rewrite (N.eqb_compare num (last_block_id st + 1)).
  assert ((num ?= last_block_id st + 1) = Eq).
  { rewrite (N.compare_eq_iff num (last_block_id st + 1)).
    assumption. }
  rewrite H. 
  magic. }
rewrite NumEq.
case_eq (negb (N.of_nat (length data) =? 512))...
* magic.
* simpl in H0.
  inversion H0.
  rewrite (N_ascii_embedding _).
  rewrite (N_ascii_embedding _).
  symmetry.
  rewrite (N.mul_comm (num / byte_range_size) byte_range_size).
  apply (N.div_mod _ _).
  + magic.
  + unfold byte_range_size.
    apply (N.mod_bound_pos _ _).
    - apply (N.le_0_l _).
    - magic.
  + unfold byte_range_size.
    assert (256 * (num / 256) <= 256 * num / 256).
    { rewrite (N.mul_comm 256 num).
      rewrite (N.div_mul num 256).
      rewrite (N.mul_div_le num 256).
      apply (N.le_refl _)...
      + magic.
      + magic. }
    assert (256 * num / 256 < 256 * 256).
    { assert (num < 65536).
      { apply (deserialized_num_less_than_two_byte_size pac num data). 
        assumption. }
      rewrite (N.mul_comm 256 num).
      rewrite (N.div_mul _ _)... }
    magics.
* magics.
* simpl in H0.
  inversion H0.
  rewrite (N_ascii_embedding _).
  rewrite (N_ascii_embedding _).
  unfold byte_range_size.
  rewrite (N.mul_comm _ 256).
  rewrite <- (N.div_mod num 256)...
  + apply (N.mod_bound_pos _ _).
    - apply (N.le_0_l _).
    - magic.
  + unfold byte_range_size.
    assert (256 * (num / 256) <= 256 * num / 256).
    { rewrite (N.mul_comm 256 num).
      rewrite (N.div_mul num 256).
      rewrite (N.mul_div_le num 256).
      apply (N.le_refl _)...
      + magic.
      + magic. }
    assert (256 * num / 256 < 256 * 256).
    { assert (num < 65536).
      { apply (deserialized_num_less_than_two_byte_size pac num data). 
        assumption. }
      rewrite (N.mul_comm 256 num).
      rewrite (N.div_mul _ _)... }
    magics.
Qed.

Theorem bad_ack_block_id_errors : forall pac st p p2 timeout num,
  normal_circumstances st p timeout -> 
  transfer_mode st = Write ->
  deserialize_packet pac = Some (p_ACK num) ->
  num <> last_block_id st + 1 ->
  let res := coq_process_packet pac st p timeout in
     [SEND_PACKET] = (orders (new_state res))
  /\ (deserialize_packet (packet_to_send res) = Some p2 ->
  match p2 with
  | p_ERROR _ _ => True
  | _ => False
  end).
Proof with magic.
intros pac st p p2 timeout num.
intros Normals WriteMode GotAck BadBlockID res.
unfold res.
unfold coq_process_packet.
destruct Normals as [NotFin [PortOK NoTimeout]].
rewrite NotFin.
rewrite NoTimeout.
rewrite PortOK.
rewrite GotAck.
rewrite WriteMode. 
destruct (two_bytes_range_size ?= num + 1)...
* case_eq (num =? last_block_id st + 1)...
* unfold deserialize_packet in H...
  unfold illegal_operation in H...
  simpl in H...
  case_eq (num =? last_block_id st + 1)...
  + rewrite H0 in H...
    simpl in H...
    inversion H...
  + rewrite H0 in H...
    simpl in H...
    inversion H...
* case_eq (num =? last_block_id st + 1)...
* case_eq (num =? last_block_id st + 1)...
  + rewrite H0 in H...
    unfold deserialize_packet in H...
    unfold illegal_operation in H...
    simpl in H...
    inversion H...
  + rewrite H0 in H...
    unfold deserialize_packet in H...
    unfold illegal_operation in H...
    simpl in H...
    inversion H...
* case_eq (num =? last_block_id st + 1)...
  case_eq (N.of_nat (length (file_contents st)) ?= 512)...
* case_eq (num =? last_block_id st + 1)...
  + rewrite H0 in H...
    exfalso.
    apply BadBlockID.
    apply (Neqb_ok num (last_block_id st + 1)).
    assumption.
  + rewrite H0 in H...
    unfold illegal_operation in H...
    simpl in H...
    inversion H...
Qed.



(*  error przechodzi w error
stan ko\u0144cowy przechodzi w error
jak odbior\u0119 blok < 512 to wchodz\u0119 w ko\u0144cowy
je\u015bli port jest ustalony to on si\u0119 nie zmienia
wysy\u0142any ack ro\u015bnie o 1 po otrzymaniu pakietu
gdy wy\u015bl\u0119 ca\u0142y plik to ko\u0144cz\u0119
po zaackowaniu bloku m\u00f3j licznik wys\u0142anych blok\u00f3w ro\u015bnie
Nie mam asercji na to jaki pakiet wysy\u0142am chyba
*)



(*
Definition coq_process_packet 
  (pack : string) 
  (st : state) (p : positive) (timeout : bool) : result.

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