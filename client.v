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

Definition send_bytes (st : state) (byte_count : nat) : forall new_id, new_id < two_bytes_range_size -> result := fun new_id prop =>
  let to_send := substring 0 byte_count (file_contents st) in
  let rest    := substring byte_count (length (file_contents st) - byte_count) (file_contents st) in
  let pac     := p_DATA new_id prop to_send in
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
      exact (illegal_operation "File too large." st).
    * intro.
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


Theorem finish_after_small_read : forall pac st p timeout num prop data,
  normal_circumstances st p timeout -> 
  transfer_mode st = Read -> 
  deserialize_packet pac = Some (p_DATA num prop data) ->
  num =? last_block_id st + 1 = true ->
  N_of_nat (length data) < 512 ->
  finished (new_state (coq_process_packet pac st p timeout)) = true.
Proof with magic.
intros pac st p timeout num prop data.
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

Theorem finish_after_small_write : forall pac st p timeout num prop,
  normal_circumstances st p timeout -> 
  transfer_mode st = Write -> 
  deserialize_packet pac = Some (p_ACK num prop) ->
  num = last_block_id st + 1 ->
  N_of_nat (length (file_contents st)) < 512 ->
  finished (new_state (coq_process_packet pac st p timeout)) = true.
Proof with magic.
intros pac st p timeout num prop.
intros Normal WriteMode PacketACK BlockIDOK PacketSmall.
unfold coq_process_packet.
unfold normal_circumstances in Normal.
destruct Normal as [FinF [PortOK TimeoutF]].
rewrite FinF.
rewrite TimeoutF.
rewrite PortOK.
rewrite PacketACK.
rewrite WriteMode.
rewrite BlockIDOK.
assert (last_block_id st + 1 < two_bytes_range_size).
{ rewrite <- BlockIDOK... }
unfold two_bytes_range_size in *.
unfold N.compare in *.

assert (exists m, last_block_id st + 1 + 1 = N.pos m).
{ destruct (last_block_id st).
  + simpl.
    exists 2%positive...
  + magics.
    exists (p0 + 1 + 1)%positive...
}
destruct H0 as [x H0].
rewrite H0.
assert (N.pos x <= 65536).
{ rewrite <- H0.
  assert (forall x, x + 1 = N.succ x).
  { magics. }
  rewrite (H1 (last_block_id st + 1)).
  apply (N.le_succ_l (last_block_id st + 1) 65536).
  assumption.
}
assert (N.pos x ?= 65536 <> Gt).
{ apply (N.compare_le_iff (N.pos x) 65536).
  assumption. 
}
assert (N.pos x < 65536 \/ N.pos x = 65536) as X.
{ apply (N.le_lteq (N.pos x) 65536). 
  assumption. }
destruct X as [X1 | X2]. 
Close Scope N_scope.
Open Scope positive_scope.
* assert (65536 ?= x = Gt) as G.
  { apply (Pos.compare_gt_iff 65536 x).
    assumption. }


Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Eqdep_dec.
(*  assert (
   (fun pf : (65536 ?= x) = Gt =>
      N.compare_gt_iff 65536 (N.pos x) pf
   ) = (
    fun pf : (65536 ?= x) = Gt =>
      N.compare_gt_iff 65536 (N.pos x) G
   )
  ).*)
  assert (
    (fun H3 : (65536 ?= x) = Gt =>
      match
        match N.of_nat (length (file_contents st)) with
        | 0%N => Lt
        | N.pos n' => n' ?= 512
        end as c
        return
          (match N.of_nat (length (file_contents st)) with
           | 0%N => Lt
           | N.pos n' => n' ?= 512
           end = c -> result)
      with
      | Eq =>
          fun
            _ : match N.of_nat (length (file_contents st)) with
                | 0%N => Lt
                | N.pos n' => n' ?= 512
                end = Eq =>
          send_bytes st 512 (N.pos x)
            (match N.compare_gt_iff 65536 (N.pos x) with
             | conj H5 _ => H5
             end H3)
      | Lt =>
          fun
            _ : match N.of_nat (length (file_contents st)) with
                | 0%N => Lt
                | N.pos n' => n' ?= 512
                end = Lt =>
          send_bytes st
            (N.to_nat (N.of_nat (length (file_contents st))))
            (N.pos x)
            (match N.compare_gt_iff 65536 (N.pos x) with
             | conj H5 _ => H5
             end H3)
      | Gt =>
          fun
            _ : match N.of_nat (length (file_contents st)) with
                | 0%N => Lt
                | N.pos n' => n' ?= 512
                end = Gt =>
          send_bytes st 512 (N.pos x)
            (match N.compare_gt_iff 65536 (N.pos x) with
             | conj H5 _ => H5
             end H3)
      end eq_refl
    ) = (fun H3 : (65536 ?= x) = Gt =>
      match
        match N.of_nat (length (file_contents st)) with
        | 0%N => Lt
        | N.pos n' => n' ?= 512
        end as c
        return
          (match N.of_nat (length (file_contents st)) with
           | 0%N => Lt
           | N.pos n' => n' ?= 512
           end = c -> result)
      with
      | Eq =>
          fun
            _ : match N.of_nat (length (file_contents st)) with
                | 0%N => Lt
                | N.pos n' => n' ?= 512
                end = Eq =>
          send_bytes st 512 (N.pos x)
            (match N.compare_gt_iff 65536 (N.pos x) with
             | conj H5 _ => H5
             end G)
      | Lt =>
          fun
            _ : match N.of_nat (length (file_contents st)) with
                | 0%N => Lt
                | N.pos n' => n' ?= 512
                end = Lt =>
          send_bytes st
            (N.to_nat (N.of_nat (length (file_contents st))))
            (N.pos x)
            (match N.compare_gt_iff 65536 (N.pos x) with
             | conj H5 _ => H5
             end G)
      | Gt =>
          fun
            _ : match N.of_nat (length (file_contents st)) with
                | 0%N => Lt
                | N.pos n' => n' ?= 512
                end = Gt =>
          send_bytes st 512 (N.pos x)
            (match N.compare_gt_iff 65536 (N.pos x) with
             | conj H5 _ => H5
             end G)
      end eq_refl
    )
  ).
  { extensionality H3.
    repeat f_equal.
    intro.
Local Close Scope positive_scope.
Local Open Scope N_scope.
    assert (N.of_nat (length (file_contents st)) ?= 512 = Lt).
    { apply (N.compare_lt_iff (N.of_nat (length (file_contents st))) 512).
      assumption. }
    admit.
  }
  Check conj.
  generalize ((65536 ?= x)%positive).
  rewrite G.
  ++++ intros ->.
    generalize (eq_refl ( N16_to_N next_block + 1 ?= 256 * 256)).
    revert H10.
    case_eq (N16_to_N next_block + 1 ?= 256 * 256);
      intros; unfold N.lt in H1; congruence + reflexivity.
  ++++ extensionality pf.
    f_equal.
    f_equal.
    apply UIP_dec.
    decide equality.
  rewrite G. (65536 ?= x = Gt).
  magics.
  
  generalize dependent (65536 ?= x).
  generalize (finished
  (new_state
     (match
        65536 ?= x as c return ((65536 ?= x) = c -> result)
      with
      | Eq =>
          fun _ : (65536 ?= x) = Eq =>
          illegal_operation "File too large." st
      | Lt =>
          fun _ : (65536 ?= x) = Lt =>
          illegal_operation "File too large." st
      | Gt =>
          fun H7 : (65536 ?= x) = Gt =>
          match
            match N.of_nat (length (file_contents st)) with
            | 0%N => Lt
            | N.pos n' => n' ?= 512
            end as c
            return
              (match
                 N.of_nat (length (file_contents st))
               with
               | 0%N => Lt
               | N.pos n' => n' ?= 512
               end = c -> result)
          with
          | Eq =>
              fun
                _ : match
                      N.of_nat (length (file_contents st))
                    with
                    | 0%N => Lt
                    | N.pos n' => n' ?= 512
                    end = Eq =>
              send_bytes st 512 (N.pos x)
                (match N.compare_gt_iff 65536 (N.pos x) with
                 | conj H9 _ => H9
                 end H7)
          | Lt =>
              fun
                _ : match
                      N.of_nat (length (file_contents st))
                    with
                    | 0%N => Lt
                    | N.pos n' => n' ?= 512
                    end = Lt =>
              send_bytes st
                (N.to_nat
                   (N.of_nat (length (file_contents st))))
                (N.pos x)
                (match N.compare_gt_iff 65536 (N.pos x) with
                 | conj H9 _ => H9
                 end H7)
          | Gt =>
              fun
                _ : match
                      N.of_nat (length (file_contents st))
                    with
                    | 0%N => Lt
                    | N.pos n' => n' ?= 512
                    end = Gt =>
              send_bytes st 512 (N.pos x)
                (match N.compare_gt_iff 65536 (N.pos x) with
                 | conj H9 _ => H9
                 end H7)
          end eq_refl
      end eq_refl)) = true).
  rewrite G.
  rewrite (N.compare_gt_iff 65536 (N.pos x)).
assert (N.pos x ?= 65536 = Lt \/ N.pos x ?= 65536 = Eq).
{ N.order. destruct H2.

destruct (last_block_id st).

* magics.
  
  elim (length (file_contents st)).
  + magics.
  + magics.
    destruct (Pos.of_succ_nat n ?= 512)%positive.
    - magics.
      exfalso.
      
destruct H as [m Hm].
magics.
rewrite Hm...
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