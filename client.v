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
refine (
  match deserialize_packet pack with
  | Some p0 => _
  | None => illegal_operation "Cannot understand package." st
  end
).
refine (
  match p0 with 
  | p_RRQ _ => illegal_operation "Cannot send read requests to client." st
  | p_WRQ _ => illegal_operation "Cannot send write requests to client." st
  | p_DATA nr data => _
  | p_ACK nr => _
  | p_ERROR _ err_msg => _
  end
).
- (* p_DATA *)
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
  refine (
    match transfer_mode st with
    | Read => illegal_operation "Cannot receive acknowledgments in read mode." st
    | Write => _
    end
  ).
  refine (
    if nr =? last_block_id st
      then _
      else illegal_operation "Incorrect block number." st
  ).
  refine (
    match nr + 1 ?= two_bytes_range_size with
    | Lt => _
    | _ => illegal_operation "File too large." st
    end
  ).
  refine (
    match N_of_nat (length (file_contents st)) ?= 512 with
    | Lt => send_bytes st (length (file_contents st)) (nr + 1)
    | _ => send_bytes st 512 (nr + 1)
    end
  ).
- (* p_ERROR *)
  exact (
    mkResult err_msg
      (mkState [PRINT] (transfer_mode st) (port st) (last_packet st) (last_block_id st) false true (file_contents st))
  ).
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
  num = last_block_id st ->
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
rewrite (N.eqb_refl _).
case_eq (last_block_id st + 1)...
* magics.
* case_eq (p0 ?= 65536)%positive...
  rewrite (N.ltb_compare (N.of_nat (length (file_contents st))) 512).
  rewrite NL...
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
destruct (transfer_mode st); magics.
* destruct (n =? last_block_id st + 1)...
  destruct (negb (N.of_nat (length s) =? 512))...
* destruct (n =? last_block_id st)...
  destruct (n + 1)...
  - destruct (N.of_nat (length (file_contents st)) ?= 512)...
  - destruct (p0 ?= 65536)%positive...
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
  num <> last_block_id st ->
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
case_eq (num =? last_block_id st)...
* exfalso. 
  apply BadBlockID.
  Search (_ =? _ = _).
  apply (Neqb_ok _ _)...
* destruct (two_bytes_range_size ?= num + 1)...
  + exfalso.
    apply BadBlockID.
    apply (Neqb_ok _ _)...
  + exfalso.
    apply BadBlockID.
    apply (Neqb_ok _ _)...
  + exfalso.
    apply BadBlockID.
    apply (Neqb_ok _ _)...
* unfold illegal_operation in H0...
  unfold illegal_operation in H0...
  simpl in H0...
  inversion H0...
Qed.

Theorem when_sending_data_new_last_block_id_is_the_same : forall pac st p p2 timeout,
  normal_circumstances st p timeout -> 
  transfer_mode st = Write ->
  let res := coq_process_packet pac st p timeout in
    deserialize_packet (packet_to_send res) = Some p2 ->
    In SEND_PACKET (orders (new_state res)) -> 
    match p2 with
    | p_DATA next_nr _ => last_block_id (new_state res) = next_nr
    | _ => True
    end.
Proof with magic.
intros pac st p p2 timeout.
intros Normals WriteMode res Deser Sending.
unfold deserialize_packet in *.
unfold res in *.
clear res.
unfold coq_process_packet in *.
destruct Normals as [NotFin [PortOK NoTimeout]].
rewrite NotFin in *.
rewrite NoTimeout in *.
rewrite PortOK in *.
unfold deserialize_packet in *.
rewrite WriteMode in *...
destruct pac...
{ simpl in *...
  inversion Deser... }
destruct pac...
{ simpl in *...
  inversion Deser... }
destruct (ascii_to_opcode a0)...
{ simpl in *...
  case_eq p0... 
  + rewrite H in *...
    unfold illegal_operation in *...
    simpl in *...
    inversion Deser...
  + rewrite H in *...
    unfold illegal_operation in *...
    simpl in *...
    inversion Deser...
  + rewrite H in *...
    destruct pac...
    { unfold illegal_operation in *...
      simpl in *...
      inversion Deser... }
    destruct pac...
    { unfold illegal_operation in *...
      simpl in *...
      inversion Deser... }
    unfold illegal_operation in *...
    simpl in *...
    inversion Deser...
  + rewrite H in *...
    destruct pac...
    { unfold illegal_operation in *...
      simpl in *...
      inversion Deser... }
    destruct pac...
    { unfold illegal_operation in *...
      simpl in *...
      inversion Deser... }
    destruct pac...
    { case_eq (N_of_ascii a1 * byte_range_size + N_of_ascii a2 =? last_block_id st)...
      { rewrite H0 in *...
        case_eq (N_of_ascii a1 * byte_range_size + N_of_ascii a2 + 1 ?= two_bytes_range_size)...
        + rewrite H1 in *...
          simpl in *...
          inversion Deser...
        + rewrite H1 in *...
          case_eq (N.of_nat (length (file_contents st)) ?= 512)...
          - rewrite H2 in *...
            unfold send_bytes in *...
            simpl in *...
            inversion Deser...
            remember (N_of_ascii a1 * byte_range_size + N_of_ascii a2 + 1) as X.
            rewrite (N_ascii_embedding _)...
            { rewrite (N_ascii_embedding _)...
              { rewrite (N.mul_comm _ _).
                apply (N.div_mod _ _)... }
              unfold byte_range_size.
              apply (N.mod_bound_pos _ _).
              apply (N.le_0_l _).
              magics. }
            apply (inequality_256 X).
            remember (N.compare_lt_iff X two_bytes_range_size) as NLT.
            destruct NLT.
            apply l.
            assumption.
          - rewrite H2 in *...
            unfold send_bytes in *...
            simpl in *...
            inversion Deser...
            remember (N_of_ascii a1 * byte_range_size + N_of_ascii a2 + 1) as X.
            rewrite (N_ascii_embedding _)...
            { rewrite (N_ascii_embedding _)...
              { rewrite (N.mul_comm _ _).
                apply (N.div_mod _ _)... }
              unfold byte_range_size.
              apply (N.mod_bound_pos _ _).
              apply (N.le_0_l _).
              magics. }
            apply (inequality_256 X).
            remember (N.compare_lt_iff X two_bytes_range_size) as NLT.
            destruct NLT.
            apply l.
            assumption.
          - rewrite H2 in *...
            unfold send_bytes in *...
            simpl in *...
            inversion Deser...
            remember (N_of_ascii a1 * byte_range_size + N_of_ascii a2 + 1) as X.
            rewrite (N_ascii_embedding _)...
            { rewrite (N_ascii_embedding _)...
              { rewrite (N.mul_comm _ _).
                apply (N.div_mod _ _)... }
              unfold byte_range_size.
              apply (N.mod_bound_pos _ _).
              apply (N.le_0_l _).
              magics. }
            apply (inequality_256 X).
            remember (N.compare_lt_iff X two_bytes_range_size) as NLT.
            destruct NLT.
            apply l.
            assumption.
        + rewrite H1 in *...
          unfold illegal_operation in *...
          simpl in *...
          inversion Deser... }
      rewrite H0 in *...
      unfold illegal_operation in *...
      simpl in *...
      inversion Deser... }
    unfold illegal_operation in *...
    simpl in *...
    inversion Deser...
  + rewrite H in *...
    simpl in *...
    destruct pac...
    { unfold illegal_operation in *...
      simpl in *...
      inversion Deser... }
    destruct pac...
    { unfold illegal_operation in *...
      simpl in *...
      inversion Deser... }
    case_eq (nr_to_err_code (N_of_ascii a1 * byte_range_size + N_of_ascii a2))...
    { rewrite H0 in *... 
      simpl in *...
      exfalso... }
    rewrite H0 in *...
    simpl in *...
    inversion Deser... }
unfold illegal_operation in *...
simpl in *...
inversion Deser...
Qed.

Theorem correctly_sending_more_after_correct_ack : forall pac st p p2 timeout num,
  normal_circumstances st p timeout -> 
  transfer_mode st = Write ->
  deserialize_packet pac = Some (p_ACK num) ->
  num = last_block_id st ->
  num + 1 < two_bytes_range_size ->
  let res := coq_process_packet pac st p timeout in
     In SEND_PACKET (orders (new_state res))
  /\ (deserialize_packet (packet_to_send res) = Some p2 ->
  match p2 with
  | p_DATA next_nr _ => next_nr = num + 1
  | _ => False
  end). 
Proof with magic.
intros pac st p p2 timeout num.
intros Normals WriteMode GotAck GoodBlockID LimitNotReached res.
unfold res.
unfold coq_process_packet.
destruct Normals as [NotFin [PortOK NoTimeout]].
rewrite NotFin.
rewrite NoTimeout.
rewrite PortOK.
rewrite GotAck.
rewrite WriteMode.
assert (num =? last_block_id st = true) as GBID.
{ apply (N.eqb_eq _ _). 
  assumption. }
rewrite GBID.
case_eq (num + 1 ?= two_bytes_range_size)...
* magic.
* unfold deserialize_packet in H0...
  unfold illegal_operation in H0...
  simpl in *...
  inversion H0...
  assert (num + 1 = two_bytes_range_size).
  { apply (N.compare_eq _ _).
    assumption. }
  magics.
* unfold send_bytes...
  destruct (N.of_nat (length (file_contents st)) ?= 512); magics.
* destruct (N.of_nat (length (file_contents st)) ?= 512)...
  + simpl in *...
    inversion H0...
    unfold byte_range_size in *...
    rewrite (N_ascii_embedding _)...
    { rewrite (N_ascii_embedding _)...
      rewrite (N.mul_comm _ _).
      symmetry.
      apply (N.div_mod (num + 1) 256).
      + magic.
      + apply (N.mod_bound_pos _ _).
        apply (N.le_0_l _).
        magic. }
    apply (inequality_256 _).
    destruct (N.compare_lt_iff (num + 1) (256 * 256)).
    apply H1; assumption.
  + simpl in *...
    inversion H0...
    unfold byte_range_size in *...
    rewrite (N_ascii_embedding _)...
    { rewrite (N_ascii_embedding _)...
      rewrite (N.mul_comm _ _).
      symmetry.
      apply (N.div_mod (num + 1) 256).
      + magic.
      + apply (N.mod_bound_pos _ _).
        apply (N.le_0_l _).
        magic. }
    apply (inequality_256 _).
    destruct (N.compare_lt_iff (num + 1) (256 * 256)).
    apply H1; assumption.
  + simpl in *...
    inversion H0...
    unfold byte_range_size in *...
    rewrite (N_ascii_embedding _)...
    { rewrite (N_ascii_embedding _)...
      rewrite (N.mul_comm _ _).
      symmetry.
      apply (N.div_mod (num + 1) 256).
      + magic.
      + apply (N.mod_bound_pos _ _).
        apply (N.le_0_l _).
        magic. }
    apply (inequality_256 _).
    destruct (N.compare_lt_iff (num + 1) (256 * 256)).
    apply H1; assumption.
* magic.
* unfold deserialize_packet in H0...
  unfold illegal_operation in H0...
  simpl in *...
  inversion H0...
  assert (two_bytes_range_size < num + 1).
  { apply (N.compare_gt_iff _ _).
    assumption. }
  magics.
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